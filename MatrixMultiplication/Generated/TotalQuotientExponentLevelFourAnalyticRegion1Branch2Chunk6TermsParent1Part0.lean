import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-31409316480395906806599190052864)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6573, 1049361, 145593, 137313, 145593, 137313,
    41884179, 4219911, 4213471, 4219911, 4213471, 2675,
    2445, 2675, 2445, 44505429, 215541419, 44505429,
    25145, 22983, 25145, 22983, 296925, 271395,
    296925, 271395, 20865, 19071, 20865, 19071,
    532629489, 2579544079, 532629489, 1049361, 2109955, 2106735,
    2109955, 2106735, 296925, 271395, 296925, 271395,
    796790745, 3858886695, 796790745, 2675, 2445, 2675,
    2445, 231141099, 1119424789, 231141099, 145593, 4219911,
    2675, 25145, 296925, 20865, 2109955, 296925,
    2675, 20865, 20865, 20865
  ]
def negativeCoefficients : Array ℕ := #[
    124160459567608711958495232, 19821868859322295084356993024, 343771751670220127798820864, 324221154431139796614119424, 343771751670220127798820864, 324221154431139796614119424,
    197792443072112653796936515584, 9963983133546463701686550528, 9948777113471623444098449408, 9963983133546463701686550528, 9948777113471623444098449408, 202117285466820815146188800,
    184738976809860520759787520, 202117285466820815146188800, 184738976809860520759787520, 51311266165853201004232704, 497004674197149668645797888, 51311266165853201004232704,
    237487810423514457796771840, 217068297751586111892750336, 237487810423514457796771840, 217068297751586111892750336, 2804377335852138810153369600, 2563253303236814725542051840,
    2804377335852138810153369600, 2563253303236814725542051840, 6306059306564809432561090560, 5763856076467648247705370624, 6306059306564809432561090560, 5763856076467648247705370624,
    1228159983711712101456150528, 11896047363041453359199420416, 1228159983711712101456150528, 19821868859322295084356993024, 9963980772363222266863943680, 9948774752288382009275842560,
    9963980772363222266863943680, 9948774752288382009275842560, 2804377335852138810153369600, 2563253303236814725542051840, 2804377335852138810153369600, 2563253303236814725542051840,
    918637184582210534108037120, 8897986909013486003174768640, 918637184582210534108037120, 202117285466820815146188800, 184738976809860520759787520, 202117285466820815146188800,
    184738976809860520759787520, 1065950174542240691829866496, 10324871296224657632512704512, 1065950174542240691829866496, 343771751670220127798820864, 9963983133546463701686550528,
    202117285466820815146188800, 237487810423514457796771840, 2804377335852138810153369600, 6306059306564809432561090560, 9963980772363222266863943680, 2804377335852138810153369600,
    202117285466820815146188800, 197064353330150294767534080, 197064353330150294767534080, 197064353330150294767534080
  ]
def negativeScales : Array ℕ := #[
    12, 20, 17, 17, 17, 17,
    25, 22, 22, 22, 22, 11,
    11, 11, 11, 25, 27, 25,
    14, 14, 14, 14, 18, 18,
    18, 18, 14, 14, 14, 14,
    28, 31, 28, 20, 21, 21,
    21, 21, 18, 18, 18, 18,
    29, 31, 29, 11, 11, 11,
    11, 27, 30, 27, 17, 22,
    11, 14, 18, 14, 21, 18,
    11, 14, 14, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12682336269758884, 20001079646967428, 17151581467967548, 17067108692403213, 17151581467967548, 17067108692403213,
    25319902058767569, 22008781141428996, 22006577764926121, 22008781141428996, 22006577764926121, 11385323176175876,
    11255618749839597, 11385323176175876, 11255618749839597, 25407477998349906, 27683389887135756, 25407477998349906,
    14617983932975378, 14488279506630054, 14617983932975378, 14488279506630054, 18179739042525978, 18050034616189703,
    18179739042525978, 18050034616189703, 14348797300150759, 14219092873814483, 14348797300150759, 14219092873814483,
    28988557084288371, 31264468953320955, 28988557084288371, 20001079646967428, 21008780799550882, 21006577422525471,
    21008780799550882, 21006577422525471, 18179739042525978, 18050034616189703, 18179739042525978, 18050034616189703,
    29569625649202875, 31845537539527922, 29569625649202875, 11385323176175876, 11255618749839597, 11385323176175876,
    11255618749839597, 27784198566544119, 30060110454814769, 27784198566544119, 17151581467967548, 22008781141428996,
    11385323176175876, 14617983932975378, 18179739042525978, 14348797300150759, 21008780799550882, 18179739042525978,
    11385323176175876, 14348797300150759, 14348797300150759, 14348797300150759
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
noncomputable def negativeCeiling : ℝ := 121736767 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 19821868859322295084356993024, coefficient := (-19821868859322295084356993024) }, { argument := 343771751670220127798820864, coefficient := (-343771751670220127798820864) }, { argument := 324221154431139796614119424, coefficient := (-324221154431139796614119424) }, { argument := 343771751670220127798820864, coefficient := (-343771751670220127798820864) }, { argument := 324221154431139796614119424, coefficient := (-324221154431139796614119424) }, { argument := 197792443072112653796936515584, coefficient := (-197792443072112653796936515584) }, { argument := 9963983133546463701686550528, coefficient := (-9963983133546463701686550528) }, { argument := 9948777113471623444098449408, coefficient := (-9948777113471623444098449408) }, { argument := 9963983133546463701686550528, coefficient := (-9963983133546463701686550528) }, { argument := 9948777113471623444098449408, coefficient := (-9948777113471623444098449408) }, { argument := 202117285466820815146188800, coefficient := (-202117285466820815146188800) }, { argument := 184738976809860520759787520, coefficient := (-184738976809860520759787520) }, { argument := 202117285466820815146188800, coefficient := (-202117285466820815146188800) }, { argument := 184738976809860520759787520, coefficient := (-184738976809860520759787520) }, { argument := 51311266165853201004232704, coefficient := (-51311266165853201004232704) }, { argument := 497004674197149668645797888, coefficient := (-497004674197149668645797888) }, { argument := 51311266165853201004232704, coefficient := (-51311266165853201004232704) }, { argument := 237487810423514457796771840, coefficient := (-237487810423514457796771840) }, { argument := 217068297751586111892750336, coefficient := (-217068297751586111892750336) }, { argument := 237487810423514457796771840, coefficient := (-237487810423514457796771840) }, { argument := 217068297751586111892750336, coefficient := (-217068297751586111892750336) }, { argument := 2804377335852138810153369600, coefficient := (-2804377335852138810153369600) }, { argument := 2563253303236814725542051840, coefficient := (-2563253303236814725542051840) }, { argument := 2804377335852138810153369600, coefficient := (-2804377335852138810153369600) }, { argument := 2563253303236814725542051840, coefficient := (-2563253303236814725542051840) }, { argument := 6306059306564809432561090560, coefficient := (-6306059306564809432561090560) }, { argument := 5763856076467648247705370624, coefficient := (-5763856076467648247705370624) }, { argument := 6306059306564809432561090560, coefficient := (-6306059306564809432561090560) }, { argument := 5763856076467648247705370624, coefficient := (-5763856076467648247705370624) }, { argument := 1228159983711712101456150528, coefficient := (-1228159983711712101456150528) }, { argument := 11896047363041453359199420416, coefficient := (-11896047363041453359199420416) }, { argument := 1228159983711712101456150528, coefficient := (-1228159983711712101456150528) }, { argument := 19821868859322295084356993024, coefficient := (-19821868859322295084356993024) }, { argument := 9963980772363222266863943680, coefficient := (-9963980772363222266863943680) }, { argument := 9948774752288382009275842560, coefficient := (-9948774752288382009275842560) }, { argument := 9963980772363222266863943680, coefficient := (-9963980772363222266863943680) }, { argument := 9948774752288382009275842560, coefficient := (-9948774752288382009275842560) }, { argument := 2804377335852138810153369600, coefficient := (-2804377335852138810153369600) }, { argument := 2563253303236814725542051840, coefficient := (-2563253303236814725542051840) }, { argument := 2804377335852138810153369600, coefficient := (-2804377335852138810153369600) }, { argument := 2563253303236814725542051840, coefficient := (-2563253303236814725542051840) }, { argument := 918637184582210534108037120, coefficient := (-918637184582210534108037120) }, { argument := 8897986909013486003174768640, coefficient := (-8897986909013486003174768640) }, { argument := 918637184582210534108037120, coefficient := (-918637184582210534108037120) }, { argument := 202117285466820815146188800, coefficient := (-202117285466820815146188800) }, { argument := 184738976809860520759787520, coefficient := (-184738976809860520759787520) }, { argument := 202117285466820815146188800, coefficient := (-202117285466820815146188800) }, { argument := 184738976809860520759787520, coefficient := (-184738976809860520759787520) }, { argument := 1065950174542240691829866496, coefficient := (-1065950174542240691829866496) }, { argument := 10324871296224657632512704512, coefficient := (-10324871296224657632512704512) }, { argument := 1065950174542240691829866496, coefficient := (-1065950174542240691829866496) }, { argument := 343771751670220127798820864, coefficient := (-343771751670220127798820864) }, { argument := 9963983133546463701686550528, coefficient := (-9963983133546463701686550528) }, { argument := 202117285466820815146188800, coefficient := (-202117285466820815146188800) }, { argument := 237487810423514457796771840, coefficient := (-237487810423514457796771840) }, { argument := 2804377335852138810153369600, coefficient := (-2804377335852138810153369600) }, { argument := 6306059306564809432561090560, coefficient := (-6306059306564809432561090560) }, { argument := 9963980772363222266863943680, coefficient := (-9963980772363222266863943680) }, { argument := 2804377335852138810153369600, coefficient := (-2804377335852138810153369600) }, { argument := 202117285466820815146188800, coefficient := (-202117285466820815146188800) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }] }

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
def constantNumerator : ℤ := (-8167301701141804030825204809728)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    20865, 20865, 72797, 25145, 20865, 19071,
    20865, 19071, 20865, 19071, 20865, 19071,
    44505429, 215541419, 44505429, 20865, 19071, 20865,
    19071, 20865, 19071, 20865, 19071, 923128737,
    4470746207, 923128737, 20865, 19071, 20865, 19071,
    463717857, 2245802527, 463717857, 137313, 4213471, 2445,
    22983, 271395, 19071, 2106735, 271395, 2445,
    19071, 19071, 19071, 19071, 19071, 68657,
    22983, 26289, 72797, 68657, 72797, 68657,
    44505429, 215541419, 44505429, 25145, 22983, 25145,
    22983, 532629489, 2579544079, 532629489
  ]
def negativeCoefficients : Array ℕ := #[
    6306059306564809432561090560, 197064353330150294767534080, 343774112853461562621427712, 237487810423514457796771840, 197064353330150294767534080, 180120502389614007740792832,
    197064353330150294767534080, 180120502389614007740792832, 197064353330150294767534080, 180120502389614007740792832, 197064353330150294767534080, 180120502389614007740792832,
    51311266165853201004232704, 497004674197149668645797888, 51311266165853201004232704, 197064353330150294767534080, 180120502389614007740792832, 197064353330150294767534080,
    180120502389614007740792832, 6306059306564809432561090560, 5763856076467648247705370624, 6306059306564809432561090560, 5763856076467648247705370624, 1064294972407858330507149312,
    10308838887379588288362840064, 1064294972407858330507149312, 197064353330150294767534080, 180120502389614007740792832, 197064353330150294767534080, 180120502389614007740792832,
    1069260578811005414475300864, 10356936113914796320812433408, 1069260578811005414475300864, 324221154431139796614119424, 9948777113471623444098449408, 184738976809860520759787520,
    217068297751586111892750336, 2563253303236814725542051840, 5763856076467648247705370624, 9948774752288382009275842560, 2563253303236814725542051840, 184738976809860520759787520,
    180120502389614007740792832, 180120502389614007740792832, 180120502389614007740792832, 5763856076467648247705370624, 180120502389614007740792832, 324223515614381231436726272,
    217068297751586111892750336, 124146292468160103022854144, 343774112853461562621427712, 324223515614381231436726272, 343774112853461562621427712, 324223515614381231436726272,
    51311266165853201004232704, 497004674197149668645797888, 51311266165853201004232704, 237487810423514457796771840, 217068297751586111892750336, 237487810423514457796771840,
    217068297751586111892750336, 1228159983711712101456150528, 11896047363041453359199420416, 1228159983711712101456150528
  ]
def negativeScales : Array ℕ := #[
    14, 14, 16, 14, 14, 14,
    14, 14, 14, 14, 14, 14,
    25, 27, 25, 14, 14, 14,
    14, 14, 14, 14, 14, 29,
    32, 29, 14, 14, 14, 14,
    28, 31, 28, 17, 22, 11,
    14, 18, 14, 21, 18, 11,
    14, 14, 14, 14, 14, 16,
    14, 14, 16, 16, 16, 16,
    25, 27, 25, 14, 14, 14,
    14, 28, 31, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14348797300150759, 14348797300150759, 16151591377029703, 14617983932975378, 14348797300150759, 14219092873814483,
    14348797300150759, 14219092873814483, 14348797300150759, 14219092873814483, 14348797300150759, 14219092873814483,
    25407477998349906, 27683389887135756, 25407477998349906, 14348797300150759, 14219092873814483, 14348797300150759,
    14219092873814483, 14348797300150759, 14219092873814483, 14348797300150759, 14219092873814483, 29781956615736132,
    32057868504028099, 29781956615736132, 14348797300150759, 14219092873814483, 14348797300150759, 14219092873814483,
    28788672043168841, 31064583931394076, 28788672043168841, 17067108692403213, 22006577764926121, 11255618749839597,
    14488279506630054, 18050034616189703, 14219092873814483, 21006577422525471, 18050034616189703, 11255618749839597,
    14219092873814483, 14219092873814483, 14219092873814483, 14219092873814483, 14219092873814483, 16067119198981524,
    14488279506630054, 14682171644318808, 16151591377029703, 16067119198981524, 16151591377029703, 16067119198981524,
    25407477998349906, 27683389887135756, 25407477998349906, 14617983932975378, 14488279506630054, 14617983932975378,
    14488279506630054, 28988557084288371, 31264468953320955, 28988557084288371
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
noncomputable def negativeCeiling : ℝ := 30041533 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6306059306564809432561090560, coefficient := (-6306059306564809432561090560) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 343774112853461562621427712, coefficient := (-343774112853461562621427712) }, { argument := 237487810423514457796771840, coefficient := (-237487810423514457796771840) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 51311266165853201004232704, coefficient := (-51311266165853201004232704) }, { argument := 497004674197149668645797888, coefficient := (-497004674197149668645797888) }, { argument := 51311266165853201004232704, coefficient := (-51311266165853201004232704) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 6306059306564809432561090560, coefficient := (-6306059306564809432561090560) }, { argument := 5763856076467648247705370624, coefficient := (-5763856076467648247705370624) }, { argument := 6306059306564809432561090560, coefficient := (-6306059306564809432561090560) }, { argument := 5763856076467648247705370624, coefficient := (-5763856076467648247705370624) }, { argument := 1064294972407858330507149312, coefficient := (-1064294972407858330507149312) }, { argument := 10308838887379588288362840064, coefficient := (-10308838887379588288362840064) }, { argument := 1064294972407858330507149312, coefficient := (-1064294972407858330507149312) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 197064353330150294767534080, coefficient := (-197064353330150294767534080) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 1069260578811005414475300864, coefficient := (-1069260578811005414475300864) }, { argument := 10356936113914796320812433408, coefficient := (-10356936113914796320812433408) }, { argument := 1069260578811005414475300864, coefficient := (-1069260578811005414475300864) }, { argument := 324221154431139796614119424, coefficient := (-324221154431139796614119424) }, { argument := 9948777113471623444098449408, coefficient := (-9948777113471623444098449408) }, { argument := 184738976809860520759787520, coefficient := (-184738976809860520759787520) }, { argument := 217068297751586111892750336, coefficient := (-217068297751586111892750336) }, { argument := 2563253303236814725542051840, coefficient := (-2563253303236814725542051840) }, { argument := 5763856076467648247705370624, coefficient := (-5763856076467648247705370624) }, { argument := 9948774752288382009275842560, coefficient := (-9948774752288382009275842560) }, { argument := 2563253303236814725542051840, coefficient := (-2563253303236814725542051840) }, { argument := 184738976809860520759787520, coefficient := (-184738976809860520759787520) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 5763856076467648247705370624, coefficient := (-5763856076467648247705370624) }, { argument := 180120502389614007740792832, coefficient := (-180120502389614007740792832) }, { argument := 324223515614381231436726272, coefficient := (-324223515614381231436726272) }, { argument := 217068297751586111892750336, coefficient := (-217068297751586111892750336) }, { argument := 124146292468160103022854144, coefficient := (-124146292468160103022854144) }, { argument := 343774112853461562621427712, coefficient := (-343774112853461562621427712) }, { argument := 324223515614381231436726272, coefficient := (-324223515614381231436726272) }, { argument := 343774112853461562621427712, coefficient := (-343774112853461562621427712) }, { argument := 324223515614381231436726272, coefficient := (-324223515614381231436726272) }, { argument := 51311266165853201004232704, coefficient := (-51311266165853201004232704) }, { argument := 497004674197149668645797888, coefficient := (-497004674197149668645797888) }, { argument := 51311266165853201004232704, coefficient := (-51311266165853201004232704) }, { argument := 237487810423514457796771840, coefficient := (-237487810423514457796771840) }, { argument := 217068297751586111892750336, coefficient := (-217068297751586111892750336) }, { argument := 237487810423514457796771840, coefficient := (-237487810423514457796771840) }, { argument := 217068297751586111892750336, coefficient := (-217068297751586111892750336) }, { argument := 1228159983711712101456150528, coefficient := (-1228159983711712101456150528) }, { argument := 11896047363041453359199420416, coefficient := (-11896047363041453359199420416) }, { argument := 1228159983711712101456150528, coefficient := (-1228159983711712101456150528) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
