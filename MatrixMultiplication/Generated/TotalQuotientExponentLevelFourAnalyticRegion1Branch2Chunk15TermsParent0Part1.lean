import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 15, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9499867436121542509125752716263424)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    603067629, 1407157801, 18293051413, 18293051413, 603067629, 225748315789,
    9046014435, 7189686711783651, 18293051413, 1407157801, 9046014435, 1407157801,
    18293051413, 18293051413, 257926060168535, 85155, 21897, 85155,
    75423, 3530283, 961035, 21897, 3530283, 85155,
    85155, 36495, 85155, 961035, 36495, 85155,
    75423, 1409375669, 147770496991, 1592818261125, 73885304857, 1409375669,
    196976122753123, 4807132639, 7190082558882205, 75649087319, 2277062829, 14379540421506383,
    2277062829, 2277062829, 195068382351, 2277062829, 75649087319, 195068382351,
    394576941764273, 2277062829, 2277062829, 4807132639, 42422679, 4447941381,
    47944362375, 2223972387, 42422679, 4076598617, 147737283239, 1181898700255,
    32612354593, 304274606370543, 28035, 1575
  ]
def negativeCoefficients : Array ℕ := #[
    1423953179046633027547422523392, 103829919305483658258666225664, 2699577901942575114725321867264, 2699577901942575114725321867264, 1423953179046633027547422523392, 33314571251445185206994906120192,
    2669912210712436926651417231360, 32379470396099457316267172560896, 2699577901942575114725321867264, 103829919305483658258666225664, 2669912210712436926651417231360, 103829919305483658258666225664,
    2699577901942575114725321867264, 2699577901942575114725321867264, 290398927116038589181161635840, 402133117848764638172282880, 413622635501586484977205248, 402133117848764638172282880,
    356175047237477250952593408, 16671290114244499713942355968, 4538359472864629487944335360, 413622635501586484977205248, 16671290114244499713942355968, 402133117848764638172282880,
    402133117848764638172282880, 344685529584655404147671040, 402133117848764638172282880, 4538359472864629487944335360, 344685529584655404147671040, 402133117848764638172282880,
    356175047237477250952593408, 1624899516859761538780626944, 170367783727365273705005449216, 1836394426181496677081284608000, 170367913688136037502617124864, 1624899516859761538780626944,
    887101593031849821460662059008, 22168986380002251844832198656, 32381253132945000802673156423680, 174434919147912455305390194688, 21002197623160028063525240832, 32379846442027565732462784937984,
    21002197623160028063525240832, 21002197623160028063525240832, 899594131525354535387664482304, 21002197623160028063525240832, 174434919147912455305390194688, 899594131525354535387664482304,
    888508283949284891671033544704, 21002197623160028063525240832, 21002197623160028063525240832, 22168986380002251844832198656, 195640075608533161859874816, 20512509077542307201940455424,
    221104345627203613294067712000, 20512524724992967726067613696, 195640075608533161859874816, 75199971379037304177475715072, 2725271854054972720512682164224, 2725272855581742871416154357760,
    75198969852267153274003521536, 171291375483585225393665212416, 264783088694501007131934720, 14875454421039382423142400
  ]
def negativeScales : Array ℕ := #[
    29, 30, 34, 34, 29, 37,
    33, 52, 34, 30, 33, 30,
    34, 34, 47, 16, 14, 16,
    16, 21, 19, 14, 21, 16,
    16, 15, 16, 19, 15, 16,
    16, 30, 37, 40, 36, 30,
    47, 32, 52, 36, 31, 53,
    31, 31, 37, 31, 36, 37,
    48, 31, 31, 32, 25, 32,
    35, 31, 25, 31, 37, 40,
    34, 48, 14, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29167744556501202, 30390136977837654, 34090576695978742, 34090576695978742, 29167744556501202, 37715924268285460,
    33074635152109720, 52674850330425822, 34090576695978742, 30390136977837654, 33074635152109720, 30390136977837654,
    34090576695978742, 34090576695978742, 47873950877731965, 16377803621883399, 14418445606380756, 16377803621883399,
    16202716915325305, 21751352409236794, 19874229450734182, 14418445606380756, 21751352409236794, 16377803621883399,
    16377803621883399, 15155411200546948, 16377803621883399, 19874229450734182, 15155411200546948, 16377803621883399,
    16202716915325305, 30392409067170429, 37104567301786868, 40534718804927879, 36104568402310006, 30392409067170429,
    47485014086666177, 32162529465031765, 52674929759606636, 36138603625786285, 31084526953030492, 53674867085377006,
    31084526953030492, 31084526953030492, 37505189001503536, 31084526953030492, 36138603625786285, 37505189001503536,
    48487299978923867, 31084526953030492, 31084526953030492, 32162529465031765, 25338332394414632, 32050490629031076,
    35480642132171395, 31050491729554214, 25338332394414632, 31924718776420632, 37104242996853413, 40104243527038113,
    34924699562217890, 48112367265325313, 14774941449737867, 10621136113284685
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
noncomputable def negativeCeiling : ℝ := 45983960389 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1423953179046633027547422523392, coefficient := (-1423953179046633027547422523392) }, { argument := 103829919305483658258666225664, coefficient := (-103829919305483658258666225664) }, { argument := 2699577901942575114725321867264, coefficient := (-2699577901942575114725321867264) }, { argument := 2699577901942575114725321867264, coefficient := (-2699577901942575114725321867264) }, { argument := 1423953179046633027547422523392, coefficient := (-1423953179046633027547422523392) }, { argument := 33314571251445185206994906120192, coefficient := (-33314571251445185206994906120192) }, { argument := 2669912210712436926651417231360, coefficient := (-2669912210712436926651417231360) }, { argument := 32379470396099457316267172560896, coefficient := (-32379470396099457316267172560896) }, { argument := 2699577901942575114725321867264, coefficient := (-2699577901942575114725321867264) }, { argument := 103829919305483658258666225664, coefficient := (-103829919305483658258666225664) }, { argument := 2669912210712436926651417231360, coefficient := (-2669912210712436926651417231360) }, { argument := 103829919305483658258666225664, coefficient := (-103829919305483658258666225664) }, { argument := 2699577901942575114725321867264, coefficient := (-2699577901942575114725321867264) }, { argument := 2699577901942575114725321867264, coefficient := (-2699577901942575114725321867264) }, { argument := 290398927116038589181161635840, coefficient := (-290398927116038589181161635840) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 1624899516859761538780626944, coefficient := (-1624899516859761538780626944) }, { argument := 170367783727365273705005449216, coefficient := (-170367783727365273705005449216) }, { argument := 1836394426181496677081284608000, coefficient := (-1836394426181496677081284608000) }, { argument := 170367913688136037502617124864, coefficient := (-170367913688136037502617124864) }, { argument := 1624899516859761538780626944, coefficient := (-1624899516859761538780626944) }, { argument := 887101593031849821460662059008, coefficient := (-887101593031849821460662059008) }, { argument := 22168986380002251844832198656, coefficient := (-22168986380002251844832198656) }, { argument := 32381253132945000802673156423680, coefficient := (-32381253132945000802673156423680) }, { argument := 174434919147912455305390194688, coefficient := (-174434919147912455305390194688) }, { argument := 21002197623160028063525240832, coefficient := (-21002197623160028063525240832) }, { argument := 32379846442027565732462784937984, coefficient := (-32379846442027565732462784937984) }, { argument := 21002197623160028063525240832, coefficient := (-21002197623160028063525240832) }, { argument := 21002197623160028063525240832, coefficient := (-21002197623160028063525240832) }, { argument := 899594131525354535387664482304, coefficient := (-899594131525354535387664482304) }, { argument := 21002197623160028063525240832, coefficient := (-21002197623160028063525240832) }, { argument := 174434919147912455305390194688, coefficient := (-174434919147912455305390194688) }, { argument := 899594131525354535387664482304, coefficient := (-899594131525354535387664482304) }, { argument := 888508283949284891671033544704, coefficient := (-888508283949284891671033544704) }, { argument := 21002197623160028063525240832, coefficient := (-21002197623160028063525240832) }, { argument := 21002197623160028063525240832, coefficient := (-21002197623160028063525240832) }, { argument := 22168986380002251844832198656, coefficient := (-22168986380002251844832198656) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 20512509077542307201940455424, coefficient := (-20512509077542307201940455424) }, { argument := 221104345627203613294067712000, coefficient := (-221104345627203613294067712000) }, { argument := 20512524724992967726067613696, coefficient := (-20512524724992967726067613696) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 75199971379037304177475715072, coefficient := (-75199971379037304177475715072) }, { argument := 2725271854054972720512682164224, coefficient := (-2725271854054972720512682164224) }, { argument := 2725272855581742871416154357760, coefficient := (-2725272855581742871416154357760) }, { argument := 75198969852267153274003521536, coefficient := (-75198969852267153274003521536) }, { argument := 171291375483585225393665212416, coefficient := (-171291375483585225393665212416) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }] }

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

end TermShard2


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-57823344058857373747650155178360832)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1074908498480805, 85155, 76068650033307, 85155, 85155, 28035,
    1575, 302687279166483, 12877207715662829, 511570675, 4808531065, 56806587165,
    3989749425, 6438602792406943, 56806587165, 511570675, 3990271425, 3990156225,
    3990271425, 3989749425, 3990156225, 151344705007713, 4808531065, 244755832818223,
    898671727580951, 146344465085, 561891789341839599, 4824542805, 11257266545, 146344465085,
    146344465085, 4824542805, 1805987190005, 72368142075, 898671727930807, 146344465085,
    11257266545, 72368142075, 11257266545, 146344465085, 146344465085, 515836493375283,
    7704006818485977, 51816085125, 280878688595738919, 815421550125, 24544461375, 561732432515659569,
    24544461375, 24544461375, 2102642191125, 24544461375, 815421550125, 2102642191125,
    15432958312790223, 24544461375, 24544461375, 51816085125, 42422679, 4447941381,
    47944362375, 2223972387, 42422679, 134393361
  ]
def negativeCoefficients : Array ℕ := #[
    605119689151941595464109916160, 402133117848764638172282880, 171291371972289036669614555136, 402133117848764638172282880, 402133117848764638172282880, 264783088694501007131934720,
    14875454421039382423142400, 170397789707995266985488285696, 7249223483728949086498374811648, 75494506538718760593155686400, 88701741926537028732756951040, 1047896575133628828767370608640,
    2355132369958554917662202265600, 7249222284167635876796465938432, 1047896575133628828767370608640, 75494506538718760593155686400, 73607515761611317562887372800, 73605390696694026222541209600,
    73607515761611317562887372800, 2355132369958554917662202265600, 73605390696694026222541209600, 170398989269308476687397158912, 88701741926537028732756951040, 275570569369226129659660337152,
    32378061259695766530296872173568, 2699578894026918142898717327360, 316316956637806256741777972133888, 1423953702343868910539982766080, 103829957462573774726873743360, 2699578894026918142898717327360,
    2699578894026918142898717327360, 1423953702343868910539982766080, 33314583494420099719508346798080, 2669913191894754207262467686400, 32378061272300657340163530162176, 2699578894026918142898717327360,
    103829957462573774726873743360, 2669913191894754207262467686400, 103829957462573774726873743360, 2699578894026918142898717327360, 2699578894026918142898717327360, 290390129918628480908626231296,
    8673940559248301608038089883648, 238959515300605850265059328000, 316241289324020845001937524883456, 1880234080917924979717177344000, 226382698705837121303740416000, 316227246719930840740587821334528,
    226382698705837121303740416000, 226382698705837121303740416000, 9696725594566690029176881152000, 226382698705837121303740416000, 1880234080917924979717177344000, 9696725594566690029176881152000,
    8687983163338305869387793432576, 226382698705837121303740416000, 226382698705837121303740416000, 238959515300605850265059328000, 195640075608533161859874816, 20512509077542307201940455424,
    221104345627203613294067712000, 20512524724992967726067613696, 195640075608533161859874816, 39665918969162534071635542016
  ]
def negativeScales : Array ℕ := #[
    49, 16, 46, 16, 16, 14,
    10, 48, 53, 28, 32, 35,
    31, 52, 35, 28, 31, 31,
    31, 31, 31, 47, 32, 47,
    49, 37, 58, 32, 33, 37,
    37, 32, 40, 36, 49, 37,
    33, 36, 33, 37, 37, 48,
    52, 35, 57, 39, 34, 58,
    34, 34, 40, 34, 39, 40,
    53, 34, 34, 35, 25, 32,
    35, 31, 25, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    49933135286844661, 16377803621883399, 46112367235751556, 16377803621883399, 16377803621883399, 14774941449737867,
    10621136113284685, 48104821373694000, 53515669312621769, 28930358332873119, 32162949093324014, 35725339180129077,
    31893650999151501, 52515669073892572, 35725339180129077, 28930358332873119, 31893839742233674, 31893798090711289,
    31893839742233674, 31893650999151501, 31893798090711289, 47104831529900071, 32162949093324014, 47798336570399104,
    49674787543779950, 37090577226163441, 58963069945099549, 32167745086685901, 33390137508022353, 37090577226163441,
    37090577226163441, 32167745086685901, 40715924798470160, 36074635682294420, 49674787544341596, 37090577226163441,
    33390137508022353, 36074635682294420, 33390137508022353, 37090577226163441, 37090577226163441, 48873907172797918,
    52774530403740742, 35592680968176556, 57962724791485414, 39568755128928788, 34514678456171111, 58962660727588233,
    34514678456171111, 34514678456171111, 40935340512764196, 34514678456171111, 39568755128928788, 40935340512764196,
    53776864154330823, 34514678456171111, 34514678456171111, 35592680968176556, 25338332394414632, 32050490629031076,
    35480642132171395, 31050491729554214, 25338332394414632, 27001886630184700
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
noncomputable def negativeCeiling : ℝ := 154392465621 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 605119689151941595464109916160, coefficient := (-605119689151941595464109916160) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 171291371972289036669614555136, coefficient := (-171291371972289036669614555136) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 170397789707995266985488285696, coefficient := (-170397789707995266985488285696) }, { argument := 7249223483728949086498374811648, coefficient := (-7249223483728949086498374811648) }, { argument := 75494506538718760593155686400, coefficient := (-75494506538718760593155686400) }, { argument := 88701741926537028732756951040, coefficient := (-88701741926537028732756951040) }, { argument := 1047896575133628828767370608640, coefficient := (-1047896575133628828767370608640) }, { argument := 2355132369958554917662202265600, coefficient := (-2355132369958554917662202265600) }, { argument := 7249222284167635876796465938432, coefficient := (-7249222284167635876796465938432) }, { argument := 1047896575133628828767370608640, coefficient := (-1047896575133628828767370608640) }, { argument := 75494506538718760593155686400, coefficient := (-75494506538718760593155686400) }, { argument := 73607515761611317562887372800, coefficient := (-73607515761611317562887372800) }, { argument := 73605390696694026222541209600, coefficient := (-73605390696694026222541209600) }, { argument := 73607515761611317562887372800, coefficient := (-73607515761611317562887372800) }, { argument := 2355132369958554917662202265600, coefficient := (-2355132369958554917662202265600) }, { argument := 73605390696694026222541209600, coefficient := (-73605390696694026222541209600) }, { argument := 170398989269308476687397158912, coefficient := (-170398989269308476687397158912) }, { argument := 88701741926537028732756951040, coefficient := (-88701741926537028732756951040) }, { argument := 275570569369226129659660337152, coefficient := (-275570569369226129659660337152) }, { argument := 32378061259695766530296872173568, coefficient := (-32378061259695766530296872173568) }, { argument := 2699578894026918142898717327360, coefficient := (-2699578894026918142898717327360) }, { argument := 316316956637806256741777972133888, coefficient := (-316316956637806256741777972133888) }, { argument := 1423953702343868910539982766080, coefficient := (-1423953702343868910539982766080) }, { argument := 103829957462573774726873743360, coefficient := (-103829957462573774726873743360) }, { argument := 2699578894026918142898717327360, coefficient := (-2699578894026918142898717327360) }, { argument := 2699578894026918142898717327360, coefficient := (-2699578894026918142898717327360) }, { argument := 1423953702343868910539982766080, coefficient := (-1423953702343868910539982766080) }, { argument := 33314583494420099719508346798080, coefficient := (-33314583494420099719508346798080) }, { argument := 2669913191894754207262467686400, coefficient := (-2669913191894754207262467686400) }, { argument := 32378061272300657340163530162176, coefficient := (-32378061272300657340163530162176) }, { argument := 2699578894026918142898717327360, coefficient := (-2699578894026918142898717327360) }, { argument := 103829957462573774726873743360, coefficient := (-103829957462573774726873743360) }, { argument := 2669913191894754207262467686400, coefficient := (-2669913191894754207262467686400) }, { argument := 103829957462573774726873743360, coefficient := (-103829957462573774726873743360) }, { argument := 2699578894026918142898717327360, coefficient := (-2699578894026918142898717327360) }, { argument := 2699578894026918142898717327360, coefficient := (-2699578894026918142898717327360) }, { argument := 290390129918628480908626231296, coefficient := (-290390129918628480908626231296) }, { argument := 8673940559248301608038089883648, coefficient := (-8673940559248301608038089883648) }, { argument := 238959515300605850265059328000, coefficient := (-238959515300605850265059328000) }, { argument := 316241289324020845001937524883456, coefficient := (-316241289324020845001937524883456) }, { argument := 1880234080917924979717177344000, coefficient := (-1880234080917924979717177344000) }, { argument := 226382698705837121303740416000, coefficient := (-226382698705837121303740416000) }, { argument := 316227246719930840740587821334528, coefficient := (-316227246719930840740587821334528) }, { argument := 226382698705837121303740416000, coefficient := (-226382698705837121303740416000) }, { argument := 226382698705837121303740416000, coefficient := (-226382698705837121303740416000) }, { argument := 9696725594566690029176881152000, coefficient := (-9696725594566690029176881152000) }, { argument := 226382698705837121303740416000, coefficient := (-226382698705837121303740416000) }, { argument := 1880234080917924979717177344000, coefficient := (-1880234080917924979717177344000) }, { argument := 9696725594566690029176881152000, coefficient := (-9696725594566690029176881152000) }, { argument := 8687983163338305869387793432576, coefficient := (-8687983163338305869387793432576) }, { argument := 226382698705837121303740416000, coefficient := (-226382698705837121303740416000) }, { argument := 226382698705837121303740416000, coefficient := (-226382698705837121303740416000) }, { argument := 238959515300605850265059328000, coefficient := (-238959515300605850265059328000) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 20512509077542307201940455424, coefficient := (-20512509077542307201940455424) }, { argument := 221104345627203613294067712000, coefficient := (-221104345627203613294067712000) }, { argument := 20512524724992967726067613696, coefficient := (-20512524724992967726067613696) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 39665918969162534071635542016, coefficient := (-39665918969162534071635542016) }] }

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

end TermShard3


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
