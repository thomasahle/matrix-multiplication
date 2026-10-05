import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8

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
def constantNumerator : ℤ := (-4064507865685782117830802144231424)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1788625, 86429355, 8415, 33563599, 8635, 275,
    8415, 4785, 8635, 134805, 165, 43214691,
    8415, 275, 165, 275, 4235, 4785,
    894311, 198113479885929, 6157, 5113847285808023, 152353, 4847,
    40910760912256591, 2489, 2489, 84233, 4585, 152353,
    84233, 1584933618680241, 4847, 4585, 6157, 118809528730025,
    2750356875, 897484875, 6534725043479059, 9061702125, 1900952153846621, 18152355375,
    8135266125, 2750356875, 897484875, 193716747, 7278435829, 14555770691,
    388534461, 2677014025, 4594860535, 2677014025, 199188707089277, 359759673,
    199179199427715, 181646829, 873551945, 1499375543, 873551945, 6157,
    6157, 912637, 198104399534999, 6157
  ]
def negativeCoefficients : Array ℕ := #[
    8446542750422719170347008000, 408151089188041984898582446080, 162769772352913672082439536640, 2535993839393234259596189630464, 167025191237957166777405276160, 5319273606304368368707174400,
    162769772352913672082439536640, 92555360749696009615504834560, 167025191237957166777405276160, 2607507921810401374340256890880, 102130053241043872679177748480, 408151216691937022379003215872,
    162769772352913672082439536640, 5319273606304368368707174400, 102130053241043872679177748480, 5319273606304368368707174400, 163833627074174545756180971520, 92555360749696009615504834560,
    8446528583323270561411366912, 446111897095671049396150075392, 119093700341876349258654810112, 11515360365397317370205075144704, 2946935606331961578464160514048, 93754615162753721756813361152,
    11515355474992639764427435933696, 96288523680665984506997506048, 96288523680665984506997506048, 1629303177017584948368405168128, 88686798126929196256445071360, 2946935606331961578464160514048,
    1629303177017584948368405168128, 446119153405956572866041348096, 93754615162753721756813361152, 88686798126929196256445071360, 119093700341876349258654810112, 4280564394532838630856274739200,
    202940517537970288160931840000, 8277836899575103859195904000, 14714892635390469192209905221632, 167158899972065000511504384000, 4280563705856392060000962347008, 167425926968825487732768768000,
    150069172179393818350583808000, 202940517537970288160931840000, 8277836899575103859195904000, 3573443254700542561880113152, 134263442994481017421419249664, 134253288366239717529462243328,
    3583597882941842453837119488, 197528770403624413809973657600, 678081730748265198183230996480, 197528770403624413809973657600, 448533093511839386060713885696, 3318197307936218093174390784,
    448511684161305492066737848320, 3350792566363882318058225664, 8057094582253101089617346560, 27658596912100290978526527488, 8057094582253101089617346560, 119093700341876349258654810112,
    119093700341876349258654810112, 8619612759653408797783752704, 446091449963138678727745994752, 119093700341876349258654810112
  ]
def negativeScales : Array ℕ := #[
    20, 26, 13, 25, 13, 8,
    13, 12, 13, 17, 7, 25,
    13, 8, 7, 8, 12, 12,
    19, 47, 12, 52, 17, 12,
    55, 11, 11, 16, 12, 17,
    16, 50, 12, 12, 12, 46,
    31, 29, 52, 33, 50, 34,
    32, 31, 29, 27, 32, 33,
    28, 31, 32, 31, 47, 28,
    47, 27, 29, 30, 29, 12,
    12, 19, 47, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20770419515838947, 26365018059009403, 13038747556217312, 25000394087410642, 13075980462416287, 8103287808412022,
    13038747556217312, 12224303209373389, 13075980462416287, 17040514482391500, 7366322214245818, 25365018509698408,
    13038747556217312, 8103287808412022, 7366322214245818, 8103287808412022, 12048146254219561, 12224303209373389,
    19770417096053478, 47493320374743345, 12588011853219132, 52183330501508867, 17217058383010669, 12242876367166401,
    55183329888817310, 11281350514981036, 11281350514981036, 16362097928865399, 12162706018482417, 17217058383010669,
    16362097928865399, 50493343840958421, 12242876367166401, 12162706018482417, 12588011853219132, 46755643876097758,
    31356971682946505, 29741312385188203, 52537047957456832, 33077134921548174, 50755643643990473, 34079437707417595,
    32921542401230820, 31356971682946505, 29741312385188203, 27529373440812874, 32760981295875949, 33760872177670700,
    28533467323006638, 31317977551330640, 32097373926922252, 31317977551330640, 47501129185226293, 28422458236895676,
    47501060320963062, 27436560940013870, 29702318253463005, 30481714628978324, 29702318253463005, 12588011853219132,
    12588011853219132, 19799681619585923, 47493254248614571, 12588011853219132
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
noncomputable def negativeCeiling : ℝ := 8797613513 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8446542750422719170347008000, coefficient := (-8446542750422719170347008000) }, { argument := 408151089188041984898582446080, coefficient := (-408151089188041984898582446080) }, { argument := 162769772352913672082439536640, coefficient := (-162769772352913672082439536640) }, { argument := 2535993839393234259596189630464, coefficient := (-2535993839393234259596189630464) }, { argument := 167025191237957166777405276160, coefficient := (-167025191237957166777405276160) }, { argument := 5319273606304368368707174400, coefficient := (-5319273606304368368707174400) }, { argument := 162769772352913672082439536640, coefficient := (-162769772352913672082439536640) }, { argument := 92555360749696009615504834560, coefficient := (-92555360749696009615504834560) }, { argument := 167025191237957166777405276160, coefficient := (-167025191237957166777405276160) }, { argument := 2607507921810401374340256890880, coefficient := (-2607507921810401374340256890880) }, { argument := 102130053241043872679177748480, coefficient := (-102130053241043872679177748480) }, { argument := 408151216691937022379003215872, coefficient := (-408151216691937022379003215872) }, { argument := 162769772352913672082439536640, coefficient := (-162769772352913672082439536640) }, { argument := 5319273606304368368707174400, coefficient := (-5319273606304368368707174400) }, { argument := 102130053241043872679177748480, coefficient := (-102130053241043872679177748480) }, { argument := 5319273606304368368707174400, coefficient := (-5319273606304368368707174400) }, { argument := 163833627074174545756180971520, coefficient := (-163833627074174545756180971520) }, { argument := 92555360749696009615504834560, coefficient := (-92555360749696009615504834560) }, { argument := 8446528583323270561411366912, coefficient := (-8446528583323270561411366912) }, { argument := 446111897095671049396150075392, coefficient := (-446111897095671049396150075392) }, { argument := 119093700341876349258654810112, coefficient := (-119093700341876349258654810112) }, { argument := 11515360365397317370205075144704, coefficient := (-11515360365397317370205075144704) }, { argument := 2946935606331961578464160514048, coefficient := (-2946935606331961578464160514048) }, { argument := 93754615162753721756813361152, coefficient := (-93754615162753721756813361152) }, { argument := 11515355474992639764427435933696, coefficient := (-11515355474992639764427435933696) }, { argument := 96288523680665984506997506048, coefficient := (-96288523680665984506997506048) }, { argument := 96288523680665984506997506048, coefficient := (-96288523680665984506997506048) }, { argument := 1629303177017584948368405168128, coefficient := (-1629303177017584948368405168128) }, { argument := 88686798126929196256445071360, coefficient := (-88686798126929196256445071360) }, { argument := 2946935606331961578464160514048, coefficient := (-2946935606331961578464160514048) }, { argument := 1629303177017584948368405168128, coefficient := (-1629303177017584948368405168128) }, { argument := 446119153405956572866041348096, coefficient := (-446119153405956572866041348096) }, { argument := 93754615162753721756813361152, coefficient := (-93754615162753721756813361152) }, { argument := 88686798126929196256445071360, coefficient := (-88686798126929196256445071360) }, { argument := 119093700341876349258654810112, coefficient := (-119093700341876349258654810112) }, { argument := 4280564394532838630856274739200, coefficient := (-4280564394532838630856274739200) }, { argument := 202940517537970288160931840000, coefficient := (-202940517537970288160931840000) }, { argument := 8277836899575103859195904000, coefficient := (-8277836899575103859195904000) }, { argument := 14714892635390469192209905221632, coefficient := (-14714892635390469192209905221632) }, { argument := 167158899972065000511504384000, coefficient := (-167158899972065000511504384000) }, { argument := 4280563705856392060000962347008, coefficient := (-4280563705856392060000962347008) }, { argument := 167425926968825487732768768000, coefficient := (-167425926968825487732768768000) }, { argument := 150069172179393818350583808000, coefficient := (-150069172179393818350583808000) }, { argument := 202940517537970288160931840000, coefficient := (-202940517537970288160931840000) }, { argument := 8277836899575103859195904000, coefficient := (-8277836899575103859195904000) }, { argument := 3573443254700542561880113152, coefficient := (-3573443254700542561880113152) }, { argument := 134263442994481017421419249664, coefficient := (-134263442994481017421419249664) }, { argument := 134253288366239717529462243328, coefficient := (-134253288366239717529462243328) }, { argument := 3583597882941842453837119488, coefficient := (-3583597882941842453837119488) }, { argument := 197528770403624413809973657600, coefficient := (-197528770403624413809973657600) }, { argument := 678081730748265198183230996480, coefficient := (-678081730748265198183230996480) }, { argument := 197528770403624413809973657600, coefficient := (-197528770403624413809973657600) }, { argument := 448533093511839386060713885696, coefficient := (-448533093511839386060713885696) }, { argument := 3318197307936218093174390784, coefficient := (-3318197307936218093174390784) }, { argument := 448511684161305492066737848320, coefficient := (-448511684161305492066737848320) }, { argument := 3350792566363882318058225664, coefficient := (-3350792566363882318058225664) }, { argument := 8057094582253101089617346560, coefficient := (-8057094582253101089617346560) }, { argument := 27658596912100290978526527488, coefficient := (-27658596912100290978526527488) }, { argument := 8057094582253101089617346560, coefficient := (-8057094582253101089617346560) }, { argument := 119093700341876349258654810112, coefficient := (-119093700341876349258654810112) }, { argument := 119093700341876349258654810112, coefficient := (-119093700341876349258654810112) }, { argument := 8619612759653408797783752704, coefficient := (-8619612759653408797783752704) }, { argument := 446091449963138678727745994752, coefficient := (-446091449963138678727745994752) }, { argument := 119093700341876349258654810112, coefficient := (-119093700341876349258654810112) }] }

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
def constantNumerator : ℤ := (-10855000995301892715910736071622656)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5113518210884713, 152353, 4847, 40908128311902641, 2489, 2489,
    84233, 4585, 152353, 84233, 1584860976840271, 4847,
    4585, 6157, 6533047217242643, 4720747125, 1540454325, 5614781943403357,
    15553619475, 6533046180548729, 31156931025, 13963473075, 4720747125, 1540454325,
    5152358137783427, 13517095111, 5152013576981373, 6824938003, 8820056735, 15138856289,
    8820056735, 152353, 152353, 43214579, 4847, 4847,
    8721, 1900952153846621, 2750356875, 897484875, 6534724006785145, 9061702125,
    950475924006421, 18152355375, 8135266125, 2750356875, 897484875, 41218850456911515,
    27032145569, 41216093969482085, 13648843637, 522928169, 2489, 2489,
    8949, 285, 97809831, 3674966617, 7349377343, 196175553,
    17668292565, 30326079531, 17668292565, 2489
  ]
def negativeCoefficients : Array ℕ := #[
    11514619354546319424930996813824, 2946935606331961578464160514048, 93754615162753721756813361152, 11514614463869323223435099242496, 96288523680665984506997506048, 96288523680665984506997506048,
    1629303177017584948368405168128, 88686798126929196256445071360, 2946935606331961578464160514048, 1629303177017584948368405168128, 446098706545742797915895627776, 93754615162753721756813361152,
    88686798126929196256445071360, 119093700341876349258654810112, 14711114506583911422546845630464, 696659312412601231010168832000, 28416366690513997580677939200, 50573459736155895893302018310144,
    573827275750379435016270643200, 14711112172156749028716332449792, 574743932740396015583389286400, 515161228389318278720677478400, 696659312412601231010168832000, 28416366690513997580677939200,
    11602079094700392262298968784896, 124673197066303801891317874688, 11601303212750523825482580885504, 125897884660275352008128462848, 162701329306143267164530933760, 558525215063702650082503426048,
    162701329306143267164530933760, 2946935606331961578464160514048, 2946935606331961578464160514048, 408150158881844859578475347968, 93754615162753721756813361152, 93754615162753721756813361152,
    168688673165746896521800974336, 4280563705856392060000962347008, 202940517537970288160931840000, 8277836899575103859195904000, 14714890300963306798379392040960, 167158899972065000511504384000,
    4280563017179945489145649954816, 167425926968825487732768768000, 150069172179393818350583808000, 202940517537970288160931840000, 8277836899575103859195904000, 11602074972399181109055549603840,
    124663767768651166277357797376, 11601299090164179083781220597760, 125888362736909036280082333696, 2469458458233993437277663002624, 96288523680665984506997506048, 96288523680665984506997506048,
    173098834555701063751129104384, 5512701737442709036660162560, 3608545840699565573293473792, 135582337326450379085676806144, 135572082947440500609319436288, 3618800219709444049650843648,
    162961235582990141393228267520, 559417427867318788501165572096, 162961235582990141393228267520, 96288523680665984506997506048
  ]
def negativeScales : Array ℕ := #[
    52, 17, 12, 55, 11, 11,
    16, 12, 17, 16, 50, 12,
    12, 12, 52, 32, 30, 52,
    33, 52, 34, 33, 32, 30,
    52, 33, 52, 32, 33, 33,
    33, 17, 17, 25, 12, 12,
    13, 50, 31, 29, 52, 33,
    49, 34, 32, 31, 29, 55,
    34, 55, 33, 28, 11, 11,
    13, 8, 26, 31, 32, 27,
    34, 34, 34, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    52183237661420135, 17217058383010669, 12242876367166401, 55183237048655029, 11281350514981036, 11281350514981036,
    16362097928865399, 12162706018482417, 17217058383010669, 16362097928865399, 50493277716785926, 12242876367166401,
    12162706018482417, 12588011853219132, 52536677490087823, 32136368058538115, 30520708760594576, 52318151418281949,
    33856531299100869, 52536677261154335, 34858834085057532, 33700938770502096, 32136368058538115, 30520708760594576,
    52194154301244038, 33654066091697714, 52194057818668612, 32668168794825878, 33038140789932310, 33817537166443772,
    33038140789932310, 17217058383010669, 17217058383010669, 25365014770644622, 12242876367166401, 12242876367166401,
    13090277856857394, 50755643643990473, 31356971682946505, 29741312385188203, 52537047728582124, 33077134921548174,
    49755643411883151, 34079437707417595, 32921542401230820, 31356971682946505, 29741312385188203, 55194153788644139,
    34653956973493070, 55194057305998973, 33668059676621209, 28962037558967796, 11281350514981036, 11281350514981036,
    13127510763056369, 8154818109052105, 26543476143931444, 31775083999094136, 32774974880888671, 27547570026125256,
    34040443575801731, 34819839952356290, 34040443575801731, 11281350514981036
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
noncomputable def negativeCeiling : ℝ := 7313010043 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11514619354546319424930996813824, coefficient := (-11514619354546319424930996813824) }, { argument := 2946935606331961578464160514048, coefficient := (-2946935606331961578464160514048) }, { argument := 93754615162753721756813361152, coefficient := (-93754615162753721756813361152) }, { argument := 11514614463869323223435099242496, coefficient := (-11514614463869323223435099242496) }, { argument := 96288523680665984506997506048, coefficient := (-96288523680665984506997506048) }, { argument := 96288523680665984506997506048, coefficient := (-96288523680665984506997506048) }, { argument := 1629303177017584948368405168128, coefficient := (-1629303177017584948368405168128) }, { argument := 88686798126929196256445071360, coefficient := (-88686798126929196256445071360) }, { argument := 2946935606331961578464160514048, coefficient := (-2946935606331961578464160514048) }, { argument := 1629303177017584948368405168128, coefficient := (-1629303177017584948368405168128) }, { argument := 446098706545742797915895627776, coefficient := (-446098706545742797915895627776) }, { argument := 93754615162753721756813361152, coefficient := (-93754615162753721756813361152) }, { argument := 88686798126929196256445071360, coefficient := (-88686798126929196256445071360) }, { argument := 119093700341876349258654810112, coefficient := (-119093700341876349258654810112) }, { argument := 14711114506583911422546845630464, coefficient := (-14711114506583911422546845630464) }, { argument := 696659312412601231010168832000, coefficient := (-696659312412601231010168832000) }, { argument := 28416366690513997580677939200, coefficient := (-28416366690513997580677939200) }, { argument := 50573459736155895893302018310144, coefficient := (-50573459736155895893302018310144) }, { argument := 573827275750379435016270643200, coefficient := (-573827275750379435016270643200) }, { argument := 14711112172156749028716332449792, coefficient := (-14711112172156749028716332449792) }, { argument := 574743932740396015583389286400, coefficient := (-574743932740396015583389286400) }, { argument := 515161228389318278720677478400, coefficient := (-515161228389318278720677478400) }, { argument := 696659312412601231010168832000, coefficient := (-696659312412601231010168832000) }, { argument := 28416366690513997580677939200, coefficient := (-28416366690513997580677939200) }, { argument := 11602079094700392262298968784896, coefficient := (-11602079094700392262298968784896) }, { argument := 124673197066303801891317874688, coefficient := (-124673197066303801891317874688) }, { argument := 11601303212750523825482580885504, coefficient := (-11601303212750523825482580885504) }, { argument := 125897884660275352008128462848, coefficient := (-125897884660275352008128462848) }, { argument := 162701329306143267164530933760, coefficient := (-162701329306143267164530933760) }, { argument := 558525215063702650082503426048, coefficient := (-558525215063702650082503426048) }, { argument := 162701329306143267164530933760, coefficient := (-162701329306143267164530933760) }, { argument := 2946935606331961578464160514048, coefficient := (-2946935606331961578464160514048) }, { argument := 2946935606331961578464160514048, coefficient := (-2946935606331961578464160514048) }, { argument := 408150158881844859578475347968, coefficient := (-408150158881844859578475347968) }, { argument := 93754615162753721756813361152, coefficient := (-93754615162753721756813361152) }, { argument := 93754615162753721756813361152, coefficient := (-93754615162753721756813361152) }, { argument := 168688673165746896521800974336, coefficient := (-168688673165746896521800974336) }, { argument := 4280563705856392060000962347008, coefficient := (-4280563705856392060000962347008) }, { argument := 202940517537970288160931840000, coefficient := (-202940517537970288160931840000) }, { argument := 8277836899575103859195904000, coefficient := (-8277836899575103859195904000) }, { argument := 14714890300963306798379392040960, coefficient := (-14714890300963306798379392040960) }, { argument := 167158899972065000511504384000, coefficient := (-167158899972065000511504384000) }, { argument := 4280563017179945489145649954816, coefficient := (-4280563017179945489145649954816) }, { argument := 167425926968825487732768768000, coefficient := (-167425926968825487732768768000) }, { argument := 150069172179393818350583808000, coefficient := (-150069172179393818350583808000) }, { argument := 202940517537970288160931840000, coefficient := (-202940517537970288160931840000) }, { argument := 8277836899575103859195904000, coefficient := (-8277836899575103859195904000) }, { argument := 11602074972399181109055549603840, coefficient := (-11602074972399181109055549603840) }, { argument := 124663767768651166277357797376, coefficient := (-124663767768651166277357797376) }, { argument := 11601299090164179083781220597760, coefficient := (-11601299090164179083781220597760) }, { argument := 125888362736909036280082333696, coefficient := (-125888362736909036280082333696) }, { argument := 2469458458233993437277663002624, coefficient := (-2469458458233993437277663002624) }, { argument := 96288523680665984506997506048, coefficient := (-96288523680665984506997506048) }, { argument := 96288523680665984506997506048, coefficient := (-96288523680665984506997506048) }, { argument := 173098834555701063751129104384, coefficient := (-173098834555701063751129104384) }, { argument := 5512701737442709036660162560, coefficient := (-5512701737442709036660162560) }, { argument := 3608545840699565573293473792, coefficient := (-3608545840699565573293473792) }, { argument := 135582337326450379085676806144, coefficient := (-135582337326450379085676806144) }, { argument := 135572082947440500609319436288, coefficient := (-135572082947440500609319436288) }, { argument := 3618800219709444049650843648, coefficient := (-3618800219709444049650843648) }, { argument := 162961235582990141393228267520, coefficient := (-162961235582990141393228267520) }, { argument := 559417427867318788501165572096, coefficient := (-559417427867318788501165572096) }, { argument := 162961235582990141393228267520, coefficient := (-162961235582990141393228267520) }, { argument := 96288523680665984506997506048, coefficient := (-96288523680665984506997506048) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8
