import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 8, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-26249061463243936063670708076544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    34743, 70707, 3441, 10545, 3441, 562187661,
    37265240691, 36309, 93639, 78351, 2191917, 37257413235,
    78351, 70707, 36309, 36309, 70707, 2191917,
    70707, 562187661, 93639, 6324495, 4925839185, 200992915347,
    19703398729, 6324495, 1584015, 6324495, 3148755, 6324495,
    7734943087, 669496571, 254875022153, 278292001, 27416555, 277997089,
    562187661, 969687065, 669496571, 27416555, 3878792925, 489347240227,
    1767, 4557, 3813, 106671, 122330726375, 3813,
    3441, 1767, 1767, 3441, 106671, 3441,
    969687065, 4557, 4557, 13965, 41307, 92169,
    4557, 46011, 93639, 4557
  ]
def negativeCoefficients : Array ℕ := #[
    328138357428680167318880256, 333904366904264004124803072, 16249663067554449180327936, 398378836494883270227394560, 16249663067554449180327936, 648158243991524026022363136,
    42963897367004017887245500416, 342928809253027896128176128, 442197675089430708165279744, 5920034180789113154212724736, 10351035374032184127868895232, 42954872924655253995242127360,
    5920034180789113154212724736, 333904366904264004124803072, 342928809253027896128176128, 342928809253027896128176128, 333904366904264004124803072, 10351035374032184127868895232,
    333904366904264004124803072, 648158243991524026022363136, 442197675089430708165279744, 116666340660455690647633920, 22716423698486259414718218240, 231729054377179864763750940672,
    22716472108507316351615893504, 116666340660455690647633920, 116879677255668141612072960, 116666340660455690647633920, 116168555271626638397276160, 116666340660455690647633920,
    69670173608690388045922304, 771876993966444753553719296, 2295710109588595426277195776, 641697665025940326503677952, 31609135841736373494087680, 641017644252407097592905728,
    648158243991524026022363136, 69873316873599838941347840, 771876993966444753553719296, 31609135841736373494087680, 69874121486709264954163200, 8815296194964391161776570368,
    16688843150461326185201664, 21519824062436973238812672, 288102134386911315197165568, 503739555094187924590166016, 8814857819494593710784512000, 288102134386911315197165568,
    16249663067554449180327936, 16688843150461326185201664, 16688843150461326185201664, 16249663067554449180327936, 503739555094187924590166016, 16249663067554449180327936,
    69873316873599838941347840, 21519824062436973238812672, 21519824062436973238812672, 527582783466196763274117120, 390133584615792869684281344, 435255796359612329701146624,
    21519824062436973238812672, 434561608486630491854733312, 442197675089430708165279744, 21519824062436973238812672
  ]
def negativeScales : Array ℕ := #[
    15, 16, 11, 13, 11, 29,
    35, 15, 16, 16, 21, 35,
    16, 16, 15, 15, 16, 21,
    16, 29, 16, 22, 32, 37,
    34, 22, 20, 22, 21, 22,
    32, 29, 37, 28, 24, 28,
    29, 29, 29, 24, 31, 38,
    10, 12, 11, 16, 36, 11,
    11, 10, 10, 11, 16, 11,
    29, 12, 12, 13, 15, 16,
    12, 15, 16, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15084434713282725, 16109565428606407, 11748612176955137, 13364271474681056, 11748612176955137, 29066476548623874,
    35117111526729437, 15148039576421043, 16514821907093107, 16257664067595541, 21063761738993282, 35116808460979612,
    16257664067595541, 16109565428606407, 15148039576421043, 15148039576421043, 16109565428606407, 21063761738993282,
    16109565428606407, 29066476548623874, 16514821907093107, 22592518857027880, 32197722382596552, 37548353693555094,
    34197725457060377, 22592518857027880, 20595154566566810, 22592518857027880, 21586350077186946, 22592518857027880,
    32848743532173214, 29318501425531288, 37890999043111160, 28052024200705968, 24708543966392326, 28050494535187063,
    29066476548623874, 29852944000381865, 29318501425531288, 24708543966392326, 31852960613371654, 38832067608262818,
    10787086325046961, 12153868655223240, 11896710819843133, 16702808487201178, 36831995862760077, 11896710819843133,
    11748612176955137, 10787086325046961, 10787086325046961, 11748612176955137, 16702808487201178, 11748612176955137,
    29852944000381865, 12153868655223240, 12153868655223240, 13769527953509885, 15334098665057291, 16491993977638611,
    12153868655223240, 15489691191769175, 16514821907093107, 12153868655223240
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
noncomputable def negativeCeiling : ℝ := 5603041 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 648158243991524026022363136, coefficient := (-648158243991524026022363136) }, { argument := 42963897367004017887245500416, coefficient := (-42963897367004017887245500416) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }, { argument := 442197675089430708165279744, coefficient := (-442197675089430708165279744) }, { argument := 5920034180789113154212724736, coefficient := (-5920034180789113154212724736) }, { argument := 10351035374032184127868895232, coefficient := (-10351035374032184127868895232) }, { argument := 42954872924655253995242127360, coefficient := (-42954872924655253995242127360) }, { argument := 5920034180789113154212724736, coefficient := (-5920034180789113154212724736) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 10351035374032184127868895232, coefficient := (-10351035374032184127868895232) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 648158243991524026022363136, coefficient := (-648158243991524026022363136) }, { argument := 442197675089430708165279744, coefficient := (-442197675089430708165279744) }, { argument := 116666340660455690647633920, coefficient := (-116666340660455690647633920) }, { argument := 22716423698486259414718218240, coefficient := (-22716423698486259414718218240) }, { argument := 231729054377179864763750940672, coefficient := (-231729054377179864763750940672) }, { argument := 22716472108507316351615893504, coefficient := (-22716472108507316351615893504) }, { argument := 116666340660455690647633920, coefficient := (-116666340660455690647633920) }, { argument := 116879677255668141612072960, coefficient := (-116879677255668141612072960) }, { argument := 116666340660455690647633920, coefficient := (-116666340660455690647633920) }, { argument := 116168555271626638397276160, coefficient := (-116168555271626638397276160) }, { argument := 116666340660455690647633920, coefficient := (-116666340660455690647633920) }, { argument := 69670173608690388045922304, coefficient := (-69670173608690388045922304) }, { argument := 771876993966444753553719296, coefficient := (-771876993966444753553719296) }, { argument := 2295710109588595426277195776, coefficient := (-2295710109588595426277195776) }, { argument := 641697665025940326503677952, coefficient := (-641697665025940326503677952) }, { argument := 31609135841736373494087680, coefficient := (-31609135841736373494087680) }, { argument := 641017644252407097592905728, coefficient := (-641017644252407097592905728) }, { argument := 648158243991524026022363136, coefficient := (-648158243991524026022363136) }, { argument := 69873316873599838941347840, coefficient := (-69873316873599838941347840) }, { argument := 771876993966444753553719296, coefficient := (-771876993966444753553719296) }, { argument := 31609135841736373494087680, coefficient := (-31609135841736373494087680) }, { argument := 69874121486709264954163200, coefficient := (-69874121486709264954163200) }, { argument := 8815296194964391161776570368, coefficient := (-8815296194964391161776570368) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 8814857819494593710784512000, coefficient := (-8814857819494593710784512000) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 69873316873599838941347840, coefficient := (-69873316873599838941347840) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 527582783466196763274117120, coefficient := (-527582783466196763274117120) }, { argument := 390133584615792869684281344, coefficient := (-390133584615792869684281344) }, { argument := 435255796359612329701146624, coefficient := (-435255796359612329701146624) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 434561608486630491854733312, coefficient := (-434561608486630491854733312) }, { argument := 442197675089430708165279744, coefficient := (-442197675089430708165279744) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 597549514024490500100299799134208
def positiveArguments : Array ℕ := #[
    41, 93, 285, 843, 1881, 93,
    939, 1911, 93, 285, 93, 1285,
    5125, 2545, 5125
  ]
def positiveCoefficients : Array ℕ := #[
    6496709326169675682670603927552, 3597763239173136423925579776, 88203227799083344586562600960, 65223965819848473233747607552, 72767662934243759283914145792, 3597763239173136423925579776,
    72651606055560754883142352896, 73928231721073803291632074752, 3597763239173136423925579776, 88203227799083344586562600960, 3597763239173136423925579776, 198844118810214206655671828480,
    198263834416799184651812864000, 196909837498830799976141946880, 198263834416799184651812864000
  ]
def positiveScales : Array ℕ := #[
    5, 6, 8, 9, 10, 6,
    9, 10, 6, 8, 6, 10,
    12, 11, 12
  ]
def negativeArguments : Array ℕ := #[
    13965, 4557, 669496571, 44213881605, 5415, 13965,
    11685, 326895, 44204542725, 11685, 10545, 5415,
    5415, 10545, 326895, 10545, 669496571, 13965,
    3148755, 2456540685, 100254319431, 9826183717, 3148755, 27416555,
    1824909333, 1767, 4557, 3813, 106671, 1824528405,
    3813, 3441, 1767, 1767, 3441, 106671,
    3441, 27416555, 4557, 6324495, 4925839185, 200992915347,
    19703398729, 6324495, 940545, 36808191, 36808191, 940545,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    527582783466196763274117120, 21519824062436973238812672, 771876993966444753553719296, 50975134904545594269216276480, 409145832075826061314621440, 527582783466196763274117120,
    7063149101098470953220833280, 12349743931341381377049231360, 50964367908964651478129049600, 7063149101098470953220833280, 398378836494883270227394560, 409145832075826061314621440,
    409145832075826061314621440, 398378836494883270227394560, 12349743931341381377049231360, 398378836494883270227394560, 771876993966444753553719296, 527582783466196763274117120,
    116168555271626638397276160, 22657588661425076208905748480, 231170721603447949603280781312, 22657637031093880484563779584, 116168555271626638397276160, 31609135841736373494087680,
    2103977213973437542205227008, 16688843150461326185201664, 21519824062436973238812672, 288102134386911315197165568, 503739555094187924590166016, 2103538033890530665200353280,
    288102134386911315197165568, 16249663067554449180327936, 16688843150461326185201664, 16688843150461326185201664, 16249663067554449180327936, 503739555094187924590166016,
    16249663067554449180327936, 31609135841736373494087680, 21519824062436973238812672, 116666340660455690647633920, 22716423698486259414718218240, 231729054377179864763750940672,
    22716472108507316351615893504, 116666340660455690647633920, 8883196367261260915031408640, 347643534946928258255916367872, 347643534946928258255916367872, 8883196367261260915031408640,
    475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    13, 12, 29, 35, 12, 13,
    13, 18, 35, 13, 13, 12,
    12, 13, 18, 13, 29, 13,
    21, 31, 36, 33, 21, 24,
    30, 10, 12, 11, 16, 30,
    11, 11, 10, 10, 11, 16,
    11, 24, 12, 22, 32, 37,
    34, 22, 19, 25, 25, 19,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5357552004618083, 6539158811107971, 8154818109052103, 9719388820935039, 10877284133344468, 6539158811107971,
    9874981347482478, 10900112062706946, 6539158811107971, 8154818109052103, 6539158811107971, 10327552644081240,
    12323336289280170, 11313449940963057, 12323336289280170
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    13769527953509885, 12153868655223240, 29318501425531288, 35363780345152980, 12402745622495697, 13769527953509885,
    13512370113670596, 18318467785067930, 35363475586138880, 13512370113670596, 13364271474681056, 12402745622495697,
    12402745622495697, 13364271474681056, 18318467785067930, 13364271474681056, 29318501425531288, 13769527953509885,
    21586350077186946, 31193980987055114, 36544873439918004, 33193984066933025, 21586350077186946, 24708543966392326,
    30765177642630532, 10787086325046961, 12153868655223240, 11896710819843133, 16702808487201178, 30764876465856659,
    11896710819843133, 11748612176955137, 10787086325046961, 10787086325046961, 11748612176955137, 16702808487201178,
    11748612176955137, 24708543966392326, 12153868655223240, 22592518857027880, 32197722382596552, 37548353693555094,
    34197725457060377, 22592518857027880, 19843137446523372, 25133523512019350, 25133523512019350, 19843137446523372,
    1584962500724866
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 72908009 / 125000000000
noncomputable def negativeCeiling : ℝ := 520129919 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 527582783466196763274117120, coefficient := (-527582783466196763274117120) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 771876993966444753553719296, coefficient := (-771876993966444753553719296) }, { argument := 50975134904545594269216276480, coefficient := (-50975134904545594269216276480) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 527582783466196763274117120, coefficient := (-527582783466196763274117120) }, { argument := 7063149101098470953220833280, coefficient := (-7063149101098470953220833280) }, { argument := 12349743931341381377049231360, coefficient := (-12349743931341381377049231360) }, { argument := 50964367908964651478129049600, coefficient := (-50964367908964651478129049600) }, { argument := 7063149101098470953220833280, coefficient := (-7063149101098470953220833280) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 12349743931341381377049231360, coefficient := (-12349743931341381377049231360) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 771876993966444753553719296, coefficient := (-771876993966444753553719296) }, { argument := 527582783466196763274117120, coefficient := (-527582783466196763274117120) }, { argument := 116168555271626638397276160, coefficient := (-116168555271626638397276160) }, { argument := 22657588661425076208905748480, coefficient := (-22657588661425076208905748480) }, { argument := 231170721603447949603280781312, coefficient := (-231170721603447949603280781312) }, { argument := 22657637031093880484563779584, coefficient := (-22657637031093880484563779584) }, { argument := 116168555271626638397276160, coefficient := (-116168555271626638397276160) }, { argument := 31609135841736373494087680, coefficient := (-31609135841736373494087680) }, { argument := 2103977213973437542205227008, coefficient := (-2103977213973437542205227008) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 2103538033890530665200353280, coefficient := (-2103538033890530665200353280) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 31609135841736373494087680, coefficient := (-31609135841736373494087680) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 116666340660455690647633920, coefficient := (-116666340660455690647633920) }, { argument := 22716423698486259414718218240, coefficient := (-22716423698486259414718218240) }, { argument := 231729054377179864763750940672, coefficient := (-231729054377179864763750940672) }, { argument := 22716472108507316351615893504, coefficient := (-22716472108507316351615893504) }, { argument := 116666340660455690647633920, coefficient := (-116666340660455690647633920) }, { argument := 8883196367261260915031408640, coefficient := (-8883196367261260915031408640) }, { argument := 347643534946928258255916367872, coefficient := (-347643534946928258255916367872) }, { argument := 347643534946928258255916367872, coefficient := (-347643534946928258255916367872) }, { argument := 8883196367261260915031408640, coefficient := (-8883196367261260915031408640) }, { argument := 6496709326169675682670603927552, coefficient := 6496709326169675682670603927552 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 65223965819848473233747607552, coefficient := 65223965819848473233747607552 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 72651606055560754883142352896, coefficient := 72651606055560754883142352896 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
