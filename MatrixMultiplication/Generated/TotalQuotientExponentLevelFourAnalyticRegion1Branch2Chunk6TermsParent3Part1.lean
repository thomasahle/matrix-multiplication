import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-648915781759336279850954472292352)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15885, 128103, 184365, 176259, 22305, 171759,
    6090219, 46215, 176259, 6090219, 22305, 177255,
    158535, 177255, 46215, 158535, 184365, 171759,
    188908629, 23295566235, 485933011647, 5823894063, 377802729, 1450399101,
    1385188995, 1450399101, 1385188995, 7794497193281, 11472544839, 41906057137087,
    6801173799, 1038320983, 27186997803, 10995243343, 7804526286145, 11472544839,
    1018732911, 47173483877055, 3934530662575425, 7995, 8331, 212295,
    176259, 1967265447359895, 212295, 7995, 7887, 3681,
    7887, 176259, 3681, 23586625866345, 8331, 15885,
    212295, 232395, 128103, 2415915, 6090219, 212295,
    2415915, 232395, 114021, 219717
  ]
def negativeCoefficients : Array ℕ := #[
    9601893322289192220103802880, 9679189016880802572961579008, 6965112772914097118584504320, 6658876751232966365766746112, 6741272601626075935455313920, 6488871557849659138073690112,
    230081968631487102429683515392, 111741013506980174618091847680, 6658876751232966365766746112, 230081968631487102429683515392, 6741272601626075935455313920, 6696504567368471698829475840,
    5989282962893913631626362880, 6696504567368471698829475840, 111741013506980174618091847680, 5989282962893913631626362880, 6965112772914097118584504320, 6488871557849659138073690112,
    435593641559793292497911808, 53715918548649322727834910720, 560242618926195735744554729472, 53715941646278746021407227904, 435576890763252859618197504, 6688785255221352849739874304,
    6388056721120984931216916480, 6688785255221352849739874304, 6388056721120984931216916480, 35103294655200688538308837376, 52907774629797587994286227456, 377456206614303455223222370304,
    62729756235485963593388654592, 2394205179970440761301794816, 62688948825555606230538387456, 50706609994119912180334723072, 35148461674085863038826577920, 52907774629797587994286227456,
    2349038161085266260784054272, 53112621102618249735249592320, 4429887706463118690432004915200, 302042560244342507867996160, 314736281350296114202411008, 8020278339846490645132738560,
    6658876751232966365766746112, 4429887967834437617972108328960, 8020278339846490645132738560, 302042560244342507867996160, 297962435603143134403362816, 278128496375090624505839616,
    297962435603143134403362816, 6658876751232966365766746112, 278128496375090624505839616, 53112359731299322195146178560, 314736281350296114202411008, 9601893322289192220103802880,
    8020278339846490645132738560, 8779634870291929595495055360, 9679189016880802572961579008, 182541376343392302663141949440, 230081968631487102429683515392, 8020278339846490645132738560,
    182541376343392302663141949440, 8779634870291929595495055360, 8615183179892477070573305856, 8300673572133358699341152256
  ]
def negativeScales : Array ℕ := #[
    13, 16, 17, 17, 14, 17,
    22, 15, 17, 22, 14, 17,
    17, 17, 15, 17, 17, 17,
    27, 34, 38, 32, 28, 30,
    30, 30, 30, 42, 33, 45,
    32, 29, 34, 33, 42, 33,
    29, 45, 51, 12, 13, 17,
    17, 50, 17, 12, 12, 11,
    12, 17, 11, 44, 13, 13,
    17, 17, 16, 21, 22, 17,
    21, 17, 16, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13955377481012500, 16966944750328079, 17492205273810185, 17427337399601406, 14445079527660976, 17390026171239616,
    22538062676690401, 15496073562648108, 17427337399601406, 22538062676690401, 14445079527660976, 17435466797943745,
    17274441855824639, 17435466797943745, 15496073562648108, 17274441855824639, 17492205273810185, 17390026171239616,
    27493113361996278, 34439336346694927, 38821966489407602, 32439336967047872, 28493057881949131, 30433802789956476,
    30367435684807596, 30433802789956476, 30367435684807596, 42825593100410964, 33417466394227137, 45252224020898632,
    32663136613298741, 29951605367156588, 34662197795599580, 33356160482657632, 42827448206900819, 33417466394227137,
    29924128719359352, 45423041384891857, 51805112975602771, 12964882331740830, 13024273962540003, 17695710867600679,
    17427337399601406, 50805113060724364, 17695710867600679, 12964882331740830, 12945260936959442, 11845882035984914,
    12945260936959442, 17427337399601406, 11845882035984914, 44423034285260439, 13024273962540003, 13955377481012500,
    17695710867600679, 17826219504887810, 16966944750328079, 21204138266025370, 22538062676690401, 17695710867600679,
    21204138266025370, 17826219504887810, 16798940034596984, 17745286973289567
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
noncomputable def negativeCeiling : ℝ := 410234777 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9601893322289192220103802880, coefficient := (-9601893322289192220103802880) }, { argument := 9679189016880802572961579008, coefficient := (-9679189016880802572961579008) }, { argument := 6965112772914097118584504320, coefficient := (-6965112772914097118584504320) }, { argument := 6658876751232966365766746112, coefficient := (-6658876751232966365766746112) }, { argument := 6741272601626075935455313920, coefficient := (-6741272601626075935455313920) }, { argument := 6488871557849659138073690112, coefficient := (-6488871557849659138073690112) }, { argument := 230081968631487102429683515392, coefficient := (-230081968631487102429683515392) }, { argument := 111741013506980174618091847680, coefficient := (-111741013506980174618091847680) }, { argument := 6658876751232966365766746112, coefficient := (-6658876751232966365766746112) }, { argument := 230081968631487102429683515392, coefficient := (-230081968631487102429683515392) }, { argument := 6741272601626075935455313920, coefficient := (-6741272601626075935455313920) }, { argument := 6696504567368471698829475840, coefficient := (-6696504567368471698829475840) }, { argument := 5989282962893913631626362880, coefficient := (-5989282962893913631626362880) }, { argument := 6696504567368471698829475840, coefficient := (-6696504567368471698829475840) }, { argument := 111741013506980174618091847680, coefficient := (-111741013506980174618091847680) }, { argument := 5989282962893913631626362880, coefficient := (-5989282962893913631626362880) }, { argument := 6965112772914097118584504320, coefficient := (-6965112772914097118584504320) }, { argument := 6488871557849659138073690112, coefficient := (-6488871557849659138073690112) }, { argument := 435593641559793292497911808, coefficient := (-435593641559793292497911808) }, { argument := 53715918548649322727834910720, coefficient := (-53715918548649322727834910720) }, { argument := 560242618926195735744554729472, coefficient := (-560242618926195735744554729472) }, { argument := 53715941646278746021407227904, coefficient := (-53715941646278746021407227904) }, { argument := 435576890763252859618197504, coefficient := (-435576890763252859618197504) }, { argument := 6688785255221352849739874304, coefficient := (-6688785255221352849739874304) }, { argument := 6388056721120984931216916480, coefficient := (-6388056721120984931216916480) }, { argument := 6688785255221352849739874304, coefficient := (-6688785255221352849739874304) }, { argument := 6388056721120984931216916480, coefficient := (-6388056721120984931216916480) }, { argument := 35103294655200688538308837376, coefficient := (-35103294655200688538308837376) }, { argument := 52907774629797587994286227456, coefficient := (-52907774629797587994286227456) }, { argument := 377456206614303455223222370304, coefficient := (-377456206614303455223222370304) }, { argument := 62729756235485963593388654592, coefficient := (-62729756235485963593388654592) }, { argument := 2394205179970440761301794816, coefficient := (-2394205179970440761301794816) }, { argument := 62688948825555606230538387456, coefficient := (-62688948825555606230538387456) }, { argument := 50706609994119912180334723072, coefficient := (-50706609994119912180334723072) }, { argument := 35148461674085863038826577920, coefficient := (-35148461674085863038826577920) }, { argument := 52907774629797587994286227456, coefficient := (-52907774629797587994286227456) }, { argument := 2349038161085266260784054272, coefficient := (-2349038161085266260784054272) }, { argument := 53112621102618249735249592320, coefficient := (-53112621102618249735249592320) }, { argument := 4429887706463118690432004915200, coefficient := (-4429887706463118690432004915200) }, { argument := 302042560244342507867996160, coefficient := (-302042560244342507867996160) }, { argument := 314736281350296114202411008, coefficient := (-314736281350296114202411008) }, { argument := 8020278339846490645132738560, coefficient := (-8020278339846490645132738560) }, { argument := 6658876751232966365766746112, coefficient := (-6658876751232966365766746112) }, { argument := 4429887967834437617972108328960, coefficient := (-4429887967834437617972108328960) }, { argument := 8020278339846490645132738560, coefficient := (-8020278339846490645132738560) }, { argument := 302042560244342507867996160, coefficient := (-302042560244342507867996160) }, { argument := 297962435603143134403362816, coefficient := (-297962435603143134403362816) }, { argument := 278128496375090624505839616, coefficient := (-278128496375090624505839616) }, { argument := 297962435603143134403362816, coefficient := (-297962435603143134403362816) }, { argument := 6658876751232966365766746112, coefficient := (-6658876751232966365766746112) }, { argument := 278128496375090624505839616, coefficient := (-278128496375090624505839616) }, { argument := 53112359731299322195146178560, coefficient := (-53112359731299322195146178560) }, { argument := 314736281350296114202411008, coefficient := (-314736281350296114202411008) }, { argument := 9601893322289192220103802880, coefficient := (-9601893322289192220103802880) }, { argument := 8020278339846490645132738560, coefficient := (-8020278339846490645132738560) }, { argument := 8779634870291929595495055360, coefficient := (-8779634870291929595495055360) }, { argument := 9679189016880802572961579008, coefficient := (-9679189016880802572961579008) }, { argument := 182541376343392302663141949440, coefficient := (-182541376343392302663141949440) }, { argument := 230081968631487102429683515392, coefficient := (-230081968631487102429683515392) }, { argument := 8020278339846490645132738560, coefficient := (-8020278339846490645132738560) }, { argument := 182541376343392302663141949440, coefficient := (-182541376343392302663141949440) }, { argument := 8779634870291929595495055360, coefficient := (-8779634870291929595495055360) }, { argument := 8615183179892477070573305856, coefficient := (-8615183179892477070573305856) }, { argument := 8300673572133358699341152256, coefficient := (-8300673572133358699341152256) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-345397229992625535863418366459904)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    114021, 6090219, 219717, 15885, 128103, 2284222081521,
    165881724278955, 1724776545148089, 165881731951275, 2284197107185, 8925, 7995,
    525, 8655, 232395, 22305, 7995, 232395,
    525, 8295, 7695, 8295, 22305, 7695,
    8925, 8655, 52813257, 867788835, 572437440879, 13884625707,
    422482653, 376608513, 13919676671, 27838200745, 754369623, 2205,
    7887, 8295, 4281, 114021, 177255, 7887,
    114021, 8295, 4095, 7605, 4095, 177255,
    7605, 2205, 4281, 8145, 3681, 7695,
    7857, 219717, 158535, 3681, 219717, 7695,
    7605, 1755, 7605, 158535
  ]
def negativeCoefficients : Array ℕ := #[
    8615183179892477070573305856, 230081968631487102429683515392, 8300673572133358699341152256, 9601893322289192220103802880, 9679189016880802572961579008, 2571805428792358584245551104,
    373532435825138548634120355840, 3883851503013152545516994691072, 373532453101667295167722291200, 2571777310189782727854653440, 337176966876892668257894400, 302042560244342507867996160,
    317343027648840158360371200, 326976655273894234596311040, 8779634870291929595495055360, 6741272601626075935455313920, 302042560244342507867996160, 8779634870291929595495055360,
    317343027648840158360371200, 313376239803229656380866560, 290708880685455359355125760, 313376239803229656380866560, 6741272601626075935455313920, 290708880685455359355125760,
    337176966876892668257894400, 326976655273894234596311040, 487116317789024746425286656, 64031514197070263700884029440, 659975435631509691962599931904, 64031534244069385804739248128,
    487089335967052432385507328, 6947200855291316627998507008, 256772713138722350059105550336, 256762082307782787355073576960, 6957831686230879332030480384, 333210179031282166278389760,
    297962435603143134403362816, 313376239803229656380866560, 323463214610639218557321216, 8615183179892477070573305856, 6696504567368471698829475840, 297962435603143134403362816,
    8615183179892477070573305856, 313376239803229656380866560, 309409451957619154401361920, 287308776817789214801264640, 309409451957619154401361920, 6696504567368471698829475840,
    287308776817789214801264640, 333210179031282166278389760, 323463214610639218557321216, 307709400023786082124431360, 278128496375090624505839616, 290708880685455359355125760,
    296829067647254419552075776, 8300673572133358699341152256, 5989282962893913631626362880, 278128496375090624505839616, 8300673572133358699341152256, 290708880685455359355125760,
    287308776817789214801264640, 265208101677959275201167360, 287308776817789214801264640, 5989282962893913631626362880
  ]
def negativeScales : Array ℕ := #[
    16, 22, 17, 13, 16, 41,
    47, 50, 47, 41, 13, 12,
    9, 13, 17, 14, 12, 17,
    9, 13, 12, 13, 14, 12,
    13, 13, 25, 29, 39, 33,
    28, 28, 33, 34, 29, 11,
    12, 13, 12, 16, 17, 12,
    16, 13, 11, 12, 11, 17,
    12, 11, 12, 12, 11, 12,
    12, 17, 17, 11, 17, 12,
    12, 10, 12, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16798940034596984, 22538062676690401, 17745286973289567, 13955377481012500, 16966944750328079, 41054840060948670,
    47237148277137004, 50615330887767092, 47237148343864172, 41054824287286399, 13123636453803825, 12964882331740830,
    9036173612553486, 13079318104254002, 17826219504887810, 14445079527660976, 12964882331740830, 17826219504887810,
    9036173612553486, 13018026265843226, 12909705616407956, 13018026265843226, 14445079527660976, 12909705616407956,
    13123636453803825, 13079318104254002, 25654396779567366, 29692768783671611, 39058327079913516, 33692769235350790,
    28654316865145525, 28488490370639308, 33696406649310505, 34696346918023592, 29490696341753658, 11106562940444883,
    12945260936959442, 13018026265843226, 12063732120196920, 16798940034596984, 17435466797943745, 12945260936959442,
    16798940034596984, 13018026265843226, 11999647760072134, 12892732536443689, 11999647760072134, 17435466797943745,
    12892732536443689, 11106562940444883, 12063732120196920, 12991699004141302, 11845882035984914, 12909705616407956,
    12939762853831857, 17745286973289567, 17274441855824639, 11845882035984914, 17745286973289567, 12909705616407956,
    12892732536443689, 10777255315595305, 12892732536443689, 17274441855824639
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
noncomputable def negativeCeiling : ℝ := 3458759067 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8615183179892477070573305856, coefficient := (-8615183179892477070573305856) }, { argument := 230081968631487102429683515392, coefficient := (-230081968631487102429683515392) }, { argument := 8300673572133358699341152256, coefficient := (-8300673572133358699341152256) }, { argument := 9601893322289192220103802880, coefficient := (-9601893322289192220103802880) }, { argument := 9679189016880802572961579008, coefficient := (-9679189016880802572961579008) }, { argument := 2571805428792358584245551104, coefficient := (-2571805428792358584245551104) }, { argument := 373532435825138548634120355840, coefficient := (-373532435825138548634120355840) }, { argument := 3883851503013152545516994691072, coefficient := (-3883851503013152545516994691072) }, { argument := 373532453101667295167722291200, coefficient := (-373532453101667295167722291200) }, { argument := 2571777310189782727854653440, coefficient := (-2571777310189782727854653440) }, { argument := 337176966876892668257894400, coefficient := (-337176966876892668257894400) }, { argument := 302042560244342507867996160, coefficient := (-302042560244342507867996160) }, { argument := 317343027648840158360371200, coefficient := (-317343027648840158360371200) }, { argument := 326976655273894234596311040, coefficient := (-326976655273894234596311040) }, { argument := 8779634870291929595495055360, coefficient := (-8779634870291929595495055360) }, { argument := 6741272601626075935455313920, coefficient := (-6741272601626075935455313920) }, { argument := 302042560244342507867996160, coefficient := (-302042560244342507867996160) }, { argument := 8779634870291929595495055360, coefficient := (-8779634870291929595495055360) }, { argument := 317343027648840158360371200, coefficient := (-317343027648840158360371200) }, { argument := 313376239803229656380866560, coefficient := (-313376239803229656380866560) }, { argument := 290708880685455359355125760, coefficient := (-290708880685455359355125760) }, { argument := 313376239803229656380866560, coefficient := (-313376239803229656380866560) }, { argument := 6741272601626075935455313920, coefficient := (-6741272601626075935455313920) }, { argument := 290708880685455359355125760, coefficient := (-290708880685455359355125760) }, { argument := 337176966876892668257894400, coefficient := (-337176966876892668257894400) }, { argument := 326976655273894234596311040, coefficient := (-326976655273894234596311040) }, { argument := 487116317789024746425286656, coefficient := (-487116317789024746425286656) }, { argument := 64031514197070263700884029440, coefficient := (-64031514197070263700884029440) }, { argument := 659975435631509691962599931904, coefficient := (-659975435631509691962599931904) }, { argument := 64031534244069385804739248128, coefficient := (-64031534244069385804739248128) }, { argument := 487089335967052432385507328, coefficient := (-487089335967052432385507328) }, { argument := 6947200855291316627998507008, coefficient := (-6947200855291316627998507008) }, { argument := 256772713138722350059105550336, coefficient := (-256772713138722350059105550336) }, { argument := 256762082307782787355073576960, coefficient := (-256762082307782787355073576960) }, { argument := 6957831686230879332030480384, coefficient := (-6957831686230879332030480384) }, { argument := 333210179031282166278389760, coefficient := (-333210179031282166278389760) }, { argument := 297962435603143134403362816, coefficient := (-297962435603143134403362816) }, { argument := 313376239803229656380866560, coefficient := (-313376239803229656380866560) }, { argument := 323463214610639218557321216, coefficient := (-323463214610639218557321216) }, { argument := 8615183179892477070573305856, coefficient := (-8615183179892477070573305856) }, { argument := 6696504567368471698829475840, coefficient := (-6696504567368471698829475840) }, { argument := 297962435603143134403362816, coefficient := (-297962435603143134403362816) }, { argument := 8615183179892477070573305856, coefficient := (-8615183179892477070573305856) }, { argument := 313376239803229656380866560, coefficient := (-313376239803229656380866560) }, { argument := 309409451957619154401361920, coefficient := (-309409451957619154401361920) }, { argument := 287308776817789214801264640, coefficient := (-287308776817789214801264640) }, { argument := 309409451957619154401361920, coefficient := (-309409451957619154401361920) }, { argument := 6696504567368471698829475840, coefficient := (-6696504567368471698829475840) }, { argument := 287308776817789214801264640, coefficient := (-287308776817789214801264640) }, { argument := 333210179031282166278389760, coefficient := (-333210179031282166278389760) }, { argument := 323463214610639218557321216, coefficient := (-323463214610639218557321216) }, { argument := 307709400023786082124431360, coefficient := (-307709400023786082124431360) }, { argument := 278128496375090624505839616, coefficient := (-278128496375090624505839616) }, { argument := 290708880685455359355125760, coefficient := (-290708880685455359355125760) }, { argument := 296829067647254419552075776, coefficient := (-296829067647254419552075776) }, { argument := 8300673572133358699341152256, coefficient := (-8300673572133358699341152256) }, { argument := 5989282962893913631626362880, coefficient := (-5989282962893913631626362880) }, { argument := 278128496375090624505839616, coefficient := (-278128496375090624505839616) }, { argument := 8300673572133358699341152256, coefficient := (-8300673572133358699341152256) }, { argument := 290708880685455359355125760, coefficient := (-290708880685455359355125760) }, { argument := 287308776817789214801264640, coefficient := (-287308776817789214801264640) }, { argument := 265208101677959275201167360, coefficient := (-265208101677959275201167360) }, { argument := 287308776817789214801264640, coefficient := (-287308776817789214801264640) }, { argument := 5989282962893913631626362880, coefficient := (-5989282962893913631626362880) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
