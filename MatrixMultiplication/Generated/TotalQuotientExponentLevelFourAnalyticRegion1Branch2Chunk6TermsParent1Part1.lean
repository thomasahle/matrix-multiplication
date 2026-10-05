import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 6, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 61767954474807936672266933239808
def positiveArguments : Array ℕ := #[
    11, 3, 1, 1, 1, 1,
    31, 371, 555, 161, 31, 643,
    323, 31, 371, 31, 45, 35,
    5, 47, 555
  ]
def positiveCoefficients : Array ℕ := #[
    871509787656907713528983453696, 475368975085586025561263702016, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168,
    599627206528856070654263296, 14352367330464877562111721472, 10735261278177907071390842880, 12456771645309139016172437504, 599627206528856070654263296, 12437428832195304949377138688,
    12495457271536807149763035136, 599627206528856070654263296, 14352367330464877562111721472, 599627206528856070654263296, 1740853180245066011576893440, 1353996917968384675670917120,
    1547425049106725343623905280, 1818224432700402278758088704, 21470522556355814142781685760
  ]
def positiveScales : Array ℕ := #[
    3, 1, 0, 0, 0, 0,
    4, 8, 9, 7, 4, 9,
    8, 4, 8, 4, 5, 5,
    2, 5, 9
  ]
def negativeArguments : Array ℕ := #[
    145593, 4219911, 2675, 25145, 296925, 20865,
    2109955, 296925, 2675, 20865, 20865, 20865,
    20865, 20865, 72797, 25145, 44505429, 215541419,
    44505429, 137313, 4213471, 2445, 22983, 271395,
    19071, 2106735, 271395, 2445, 19071, 19071,
    19071, 19071, 19071, 68657, 22983, 6573,
    1049361, 41884179, 1049361, 26289, 3, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    343771751670220127798820864, 9963983133546463701686550528, 202117285466820815146188800, 237487810423514457796771840, 2804377335852138810153369600, 6306059306564809432561090560,
    9963980772363222266863943680, 2804377335852138810153369600, 202117285466820815146188800, 197064353330150294767534080, 197064353330150294767534080, 197064353330150294767534080,
    6306059306564809432561090560, 197064353330150294767534080, 343774112853461562621427712, 237487810423514457796771840, 51311266165853201004232704, 497004674197149668645797888,
    51311266165853201004232704, 324221154431139796614119424, 9948777113471623444098449408, 184738976809860520759787520, 217068297751586111892750336, 2563253303236814725542051840,
    5763856076467648247705370624, 9948774752288382009275842560, 2563253303236814725542051840, 184738976809860520759787520, 180120502389614007740792832, 180120502389614007740792832,
    180120502389614007740792832, 5763856076467648247705370624, 180120502389614007740792832, 324223515614381231436726272, 217068297751586111892750336, 124160459567608711958495232,
    19821868859322295084356993024, 197792443072112653796936515584, 19821868859322295084356993024, 124146292468160103022854144, 475368975085586025561263702016, 158456325028528675187087900672,
    79228162514264337593543950336
  ]
def negativeScales : Array ℕ := #[
    17, 22, 11, 14, 18, 14,
    21, 18, 11, 14, 14, 14,
    14, 14, 16, 14, 25, 27,
    25, 17, 22, 11, 14, 18,
    14, 21, 18, 11, 14, 14,
    14, 14, 14, 16, 14, 12,
    20, 25, 20, 14, 1, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 1584962500720924, 0, 0, 0, 0,
    4954196309696329, 8535275376620750, 9116343961237468, 7330916878114616, 4954196309696329, 9328674927327946,
    8335390354693924, 4954196309696329, 8535275376620750, 4954196309696329, 5491853096329661, 5129283016944966,
    2321928094887362, 5554588851677541, 9116343961237468
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    17151581467967548, 22008781141428996, 11385323176175876, 14617983932975378, 18179739042525978, 14348797300150759,
    21008780799550882, 18179739042525978, 11385323176175876, 14348797300150759, 14348797300150759, 14348797300150759,
    14348797300150759, 14348797300150759, 16151591377029703, 14617983932975378, 25407477998349906, 27683389887135756,
    25407477998349906, 17067108692403213, 22006577764926121, 11255618749839597, 14488279506630054, 18050034616189703,
    14219092873814483, 21006577422525471, 18050034616189703, 11255618749839597, 14219092873814483, 14219092873814483,
    14219092873814483, 14219092873814483, 14219092873814483, 16067119198981524, 14488279506630054, 12682336269758884,
    20001079646967428, 25319902058767569, 20001079646967428, 14682171644318808, 1584962500724866, 0,
    0
  ]

abbrev PositiveTerm := Fin 21
abbrev NegativeTerm := Fin 43
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
noncomputable def positiveFloor : ℝ := 7012419 / 125000000000
noncomputable def negativeCeiling : ℝ := 24182113 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 343771751670220127798820864, coefficient := (-343771751670220127798820864) }, { argument := 9963983133546463701686550528, coefficient := (-9963983133546463701686550528) }, { argument := 202117285466820815146188800, coefficient := (-202117285466820815146188800) }, { argument := 237487810423514457796771840, coefficient := (-237487810423514457796771840) }, { argument := 2804377335852138810153369600, coefficient := (-2804377335852138810153369600) }, { argument := 6306059306564809432561090560, coefficient := (-6306059306564809432561090560) }, { argument := 9963980772363222266863943680, coefficient := (-9963980772363222266863943680) }, { argument := 2804377335852138810153369600, coefficient := (-2804377335852138810153369600) }, { argument := 202117285466820815146188800, coefficient := (-202117285466820815146188800) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 6306059306564809432561090560, coefficient := (-6306059306564809432561090560) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 343774112853461562621427712, coefficient := (-343774112853461562621427712) }, { argument := 237487810423514457796771840, coefficient := (-237487810423514457796771840) }, { argument := 51311266165853201004232704, coefficient := (-51311266165853201004232704) }, { argument := 497004674197149668645797888, coefficient := (-497004674197149668645797888) }, { argument := 51311266165853201004232704, coefficient := (-51311266165853201004232704) }, { argument := 324221154431139796614119424, coefficient := (-324221154431139796614119424) }, { argument := 9948777113471623444098449408, coefficient := (-9948777113471623444098449408) }, { argument := 184738976809860520759787520, coefficient := (-184738976809860520759787520) }, { argument := 217068297751586111892750336, coefficient := (-217068297751586111892750336) }, { argument := 2563253303236814725542051840, coefficient := (-2563253303236814725542051840) }, { argument := 5763856076467648247705370624, coefficient := (-5763856076467648247705370624) }, { argument := 9948774752288382009275842560, coefficient := (-9948774752288382009275842560) }, { argument := 2563253303236814725542051840, coefficient := (-2563253303236814725542051840) }, { argument := 184738976809860520759787520, coefficient := (-184738976809860520759787520) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 5763856076467648247705370624, coefficient := (-5763856076467648247705370624) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 324223515614381231436726272, coefficient := (-324223515614381231436726272) }, { argument := 217068297751586111892750336, coefficient := (-217068297751586111892750336) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 19821868859322295084356993024, coefficient := (-19821868859322295084356993024) }, { argument := 197792443072112653796936515584, coefficient := (-197792443072112653796936515584) }, { argument := 19821868859322295084356993024, coefficient := (-19821868859322295084356993024) }, { argument := 124146292468160103022854144, coefficient := (-124146292468160103022854144) }, { argument := 871509787656907713528983453696, coefficient := 871509787656907713528983453696 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 14352367330464877562111721472, coefficient := 14352367330464877562111721472 }, { argument := 10735261278177907071390842880, coefficient := 10735261278177907071390842880 }, { argument := 12456771645309139016172437504, coefficient := 12456771645309139016172437504 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 12437428832195304949377138688, coefficient := 12437428832195304949377138688 }, { argument := 12495457271536807149763035136, coefficient := 12495457271536807149763035136 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 14352367330464877562111721472, coefficient := 14352367330464877562111721472 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 21470522556355814142781685760, coefficient := 21470522556355814142781685760 }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-22182051742975585482780794945536)
def positiveArguments : Array ℕ := #[
    39, 35, 555, 5, 39, 39,
    39, 39, 39, 45, 47, 6573,
    1049361, 41884179, 1049361, 26289, 49293, 4145011,
    2072505, 24647, 1435659, 6952949, 1435659, 535,
    489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    48279661532129830721065844736, 1353996917968384675670917120, 21470522556355814142781685760, 1547425049106725343623905280, 1508739422879057210033307648, 1508739422879057210033307648,
    1508739422879057210033307648, 48279661532129830721065844736, 1508739422879057210033307648, 1740853180245066011576893440, 1818224432700402278758088704, 248320919135217423916990464,
    39643737718644590168713986048, 395584886144225307593873031168, 39643737718644590168713986048, 248292584936320206045708288, 931118444160373686074867712, 78297044070103963907469082624,
    78297025180638032428888227840, 931137333626305164655722496, 6779707942430151977849585664, 65668746629404033637844779008, 6779707942430151977849585664, 41393620063604902941939466240,
    37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    5, 5, 9, 2, 5, 5,
    5, 5, 5, 5, 5, 12,
    20, 25, 20, 14, 15, 21,
    20, 14, 20, 22, 20, 9,
    8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 475368975085586025561263702016, 158456325028528675187087900672, 79228162514264337593543950336, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 1, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5285402218862248, 5129283016944966, 9116343961237468, 2321928094887362, 5285402218862248, 5285402218862248,
    5285402218862248, 5285402218862248, 5285402218862248, 5491853096329661, 5554588851677541, 12682336269708427,
    20001079646967427, 25319902058767568, 20001079646967427, 14682171644268551, 15589095166470589, 21982944498554210,
    20982944150498393, 14589124433920475, 20453281687963018, 22729193576691355, 20453281687963018, 9063395081288509,
    8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 0, 0, 0
  ]

abbrev PositiveTerm := Fin 27
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 114144177 / 500000000000
noncomputable def negativeCeiling : ℝ := 9069229 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 48279661532129830721065844736, coefficient := 48279661532129830721065844736 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 21470522556355814142781685760, coefficient := 21470522556355814142781685760 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 48279661532129830721065844736, coefficient := 48279661532129830721065844736 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 248320919135217423916990464, coefficient := 248320919135217423916990464 }, { argument := 39643737718644590168713986048, coefficient := 39643737718644590168713986048 }, { argument := 395584886144225307593873031168, coefficient := 395584886144225307593873031168 }, { argument := 39643737718644590168713986048, coefficient := 39643737718644590168713986048 }, { argument := 248292584936320206045708288, coefficient := 248292584936320206045708288 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 931118444160373686074867712, coefficient := 931118444160373686074867712 }, { argument := 78297044070103963907469082624, coefficient := 78297044070103963907469082624 }, { argument := 78297025180638032428888227840, coefficient := 78297025180638032428888227840 }, { argument := 931137333626305164655722496, coefficient := 931137333626305164655722496 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 6779707942430151977849585664, coefficient := 6779707942430151977849585664 }, { argument := 65668746629404033637844779008, coefficient := 65668746629404033637844779008 }, { argument := 6779707942430151977849585664, coefficient := 6779707942430151977849585664 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
