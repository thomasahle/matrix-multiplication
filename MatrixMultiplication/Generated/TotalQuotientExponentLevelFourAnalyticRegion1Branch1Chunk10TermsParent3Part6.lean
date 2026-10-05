import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 1,
parent chunk 10, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3481257916710900894149204672249856)
def positiveArguments : Array ℕ := #[
    1155, 1401, 40629, 35959, 2335, 1401,
    2335, 71451, 2335, 1401, 1144617, 73319,
    40629, 71451, 2335, 73319, 2335, 71451,
    2335, 1401, 38869, 28945, 30599, 2481,
    531761, 961801, 28945, 531761, 15713, 15713,
    30599, 30599, 961801, 30599, 38869, 2481,
    837, 2565, 7587, 16929, 837, 8451,
    17199, 837, 2565, 837, 257, 1025,
    509, 1025, 1, 1, 1, 1,
    93, 2253, 1707, 951
  ]
def positiveCoefficients : Array ℕ := #[
    89363796585913388594280529920, 216794249379852220641709129728, 3143516616007857199304782381056, 5564385734082873663137200996352, 180661874483210183868090941440, 3468707990077635530267346075648,
    180661874483210183868090941440, 5528253359186231626363582808064, 5781179983462725883778910126080, 3468707990077635530267346075648, 88560450871669632132138179493888, 5672782858772799773458055561216,
    3143516616007857199304782381056, 5528253359186231626363582808064, 180661874483210183868090941440, 5672782858772799773458055561216, 180661874483210183868090941440, 5528253359186231626363582808064,
    5781179983462725883778910126080, 216794249379852220641709129728, 751835802921616342266469679104, 559877725579927063389924229120, 591870738470208609869348470784, 767832309366757115506181799936,
    10285753644225517193134893694976, 18603936995698719277785196527616, 559877725579927063389924229120, 10285753644225517193134893694976, 607867244915349383109060591616, 607867244915349383109060591616,
    591870738470208609869348470784, 591870738470208609869348470784, 18603936995698719277785196527616, 591870738470208609869348470784, 751835802921616342266469679104, 767832309366757115506181799936,
    32379869152558227815330217984, 793829050191750101279063408640, 587015692378636259103728467968, 654908966408193833555227312128, 32379869152558227815330217984, 653864454500046793948281176064,
    665354085489664229624688672768, 32379869152558227815330217984, 793829050191750101279063408640, 32379869152558227815330217984, 39768823762042841331134365696, 39652766883359836930362572800,
    39381967499766159995228389376, 39652766883359836930362572800, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168,
    7195526478346272847851159552, 174317431781872609959232929792, 132072727941259008078300315648, 147160122170049580178633392128
  ]
def positiveScales : Array ℕ := #[
    10, 10, 15, 15, 11, 10,
    11, 16, 11, 10, 20, 16,
    15, 16, 11, 16, 11, 16,
    11, 10, 15, 14, 14, 11,
    19, 19, 14, 19, 13, 13,
    14, 14, 19, 14, 15, 11,
    9, 11, 12, 14, 9, 13,
    14, 9, 11, 9, 8, 10,
    8, 10, 0, 0, 0, 0,
    6, 11, 10, 9
  ]
def negativeArguments : Array ℕ := #[
    33, 467, 827, 27, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    10458117451882892562347801444352, 147998207576645782624740099227648, 65521690399296607189860846927872, 4278320775770274230051373318144, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    5, 8, 9, 4, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10173677136303419, 10452241240430814, 15310222235558389, 15134065280404563, 11189206834597024, 10452241240430814,
    11189206834597024, 16124666582402313, 11189206834597024, 10452241240430814, 20126433508576501, 16161899488601288,
    15310222235558389, 16124666582402313, 11189206834597024, 16161899488601288, 11189206834597024, 16124666582402313,
    11189206834597024, 10452241240430814, 15246332370848911, 14821026536055186, 14901196884524413, 11276706019892430,
    19020418446499221, 19875378900471935, 14821026536055186, 19020418446499221, 13939671032074786, 13939671032074786,
    14901196884524413, 14901196884524413, 19875378900471935, 14901196884524413, 15246332370848911, 11276706019892430,
    9709083812544787, 11324743110494416, 12889313822161717, 14047209134965507, 9709083812544787, 13044906349096086,
    14070037064419768, 9709083812544787, 11324743110494416, 9709083812544787, 8005624549193878, 10001408194392808,
    8991521844801183, 10001408194392808, 0, 0, 0, 0,
    6539158811107971, 11137631598235427, 10737247343017206, 9893301530621223
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5044394119358454, 8867278742109862, 9691743519230811, 4754887502413606, 0, 0
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 47295557407 / 1000000000000
noncomputable def negativeCeiling : ℝ := 4864077097 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 10458117451882892562347801444352, coefficient := (-10458117451882892562347801444352) }, { argument := 216794249379852220641709129728, coefficient := 216794249379852220641709129728 }, { argument := 3143516616007857199304782381056, coefficient := 3143516616007857199304782381056 }, { argument := 5564385734082873663137200996352, coefficient := 5564385734082873663137200996352 }, { argument := 180661874483210183868090941440, coefficient := 180661874483210183868090941440 }, { argument := 3468707990077635530267346075648, coefficient := 3468707990077635530267346075648 }, { argument := 180661874483210183868090941440, coefficient := 180661874483210183868090941440 }, { argument := 5528253359186231626363582808064, coefficient := 5528253359186231626363582808064 }, { argument := 5781179983462725883778910126080, coefficient := 5781179983462725883778910126080 }, { argument := 3468707990077635530267346075648, coefficient := 3468707990077635530267346075648 }, { argument := 88560450871669632132138179493888, coefficient := 88560450871669632132138179493888 }, { argument := 5672782858772799773458055561216, coefficient := 5672782858772799773458055561216 }, { argument := 3143516616007857199304782381056, coefficient := 3143516616007857199304782381056 }, { argument := 5528253359186231626363582808064, coefficient := 5528253359186231626363582808064 }, { argument := 180661874483210183868090941440, coefficient := 180661874483210183868090941440 }, { argument := 5672782858772799773458055561216, coefficient := 5672782858772799773458055561216 }, { argument := 180661874483210183868090941440, coefficient := 180661874483210183868090941440 }, { argument := 5528253359186231626363582808064, coefficient := 5528253359186231626363582808064 }, { argument := 5781179983462725883778910126080, coefficient := 5781179983462725883778910126080 }, { argument := 216794249379852220641709129728, coefficient := 216794249379852220641709129728 }, { argument := 147998207576645782624740099227648, coefficient := (-147998207576645782624740099227648) }, { argument := 751835802921616342266469679104, coefficient := 751835802921616342266469679104 }, { argument := 559877725579927063389924229120, coefficient := 559877725579927063389924229120 }, { argument := 591870738470208609869348470784, coefficient := 591870738470208609869348470784 }, { argument := 767832309366757115506181799936, coefficient := 767832309366757115506181799936 }, { argument := 10285753644225517193134893694976, coefficient := 10285753644225517193134893694976 }, { argument := 18603936995698719277785196527616, coefficient := 18603936995698719277785196527616 }, { argument := 559877725579927063389924229120, coefficient := 559877725579927063389924229120 }, { argument := 10285753644225517193134893694976, coefficient := 10285753644225517193134893694976 }, { argument := 607867244915349383109060591616, coefficient := 607867244915349383109060591616 }, { argument := 607867244915349383109060591616, coefficient := 607867244915349383109060591616 }, { argument := 591870738470208609869348470784, coefficient := 591870738470208609869348470784 }, { argument := 591870738470208609869348470784, coefficient := 591870738470208609869348470784 }, { argument := 18603936995698719277785196527616, coefficient := 18603936995698719277785196527616 }, { argument := 591870738470208609869348470784, coefficient := 591870738470208609869348470784 }, { argument := 751835802921616342266469679104, coefficient := 751835802921616342266469679104 }, { argument := 767832309366757115506181799936, coefficient := 767832309366757115506181799936 }, { argument := 65521690399296607189860846927872, coefficient := (-65521690399296607189860846927872) }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 793829050191750101279063408640, coefficient := 793829050191750101279063408640 }, { argument := 587015692378636259103728467968, coefficient := 587015692378636259103728467968 }, { argument := 654908966408193833555227312128, coefficient := 654908966408193833555227312128 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 653864454500046793948281176064, coefficient := 653864454500046793948281176064 }, { argument := 665354085489664229624688672768, coefficient := 665354085489664229624688672768 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 793829050191750101279063408640, coefficient := 793829050191750101279063408640 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 4278320775770274230051373318144, coefficient := (-4278320775770274230051373318144) }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 174317431781872609959232929792, coefficient := 174317431781872609959232929792 }, { argument := 132072727941259008078300315648, coefficient := 132072727941259008078300315648 }, { argument := 147160122170049580178633392128, coefficient := 147160122170049580178633392128 }] }

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

end TermShard12


end Parent3

namespace Parent3

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-137218080281962627904711958925934592)
def positiveArguments : Array ℕ := #[
    93, 951, 1899, 93, 2253, 93,
    291, 873, 1843, 4753, 3977, 111259,
    3395, 3977, 3589, 1843, 1843, 3589,
    111259, 3589, 291, 4753, 99, 1485,
    2607, 99, 825, 99, 2607, 5181,
    825, 79959, 5115, 1485, 2607, 99,
    5115, 99, 2607, 2607, 99, 1,
    1098907601, 1098907695, 5974208203, 21824270033, 1493514393, 3898913725,
    152963838587, 152963857371, 3898940909, 120410905, 6030823703, 124784091041,
    1507708259, 120410905
  ]
def positiveCoefficients : Array ℕ := #[
    7195526478346272847851159552, 147160122170049580178633392128, 146928008412683571377089806336, 7195526478346272847851159552, 174317431781872609959232929792, 7195526478346272847851159552,
    90060137858011414998911287296, 67545103393508561249183465472, 71297609137592370207471435776, 91936390730053319478055272448, 1230821884059489338318454259712, 2152062044232064437578150969344,
    65668850521466656770039480320, 1230821884059489338318454259712, 69421356265550465728327450624, 71297609137592370207471435776, 71297609137592370207471435776, 69421356265550465728327450624,
    2152062044232064437578150969344, 69421356265550465728327450624, 90060137858011414998911287296, 91936390730053319478055272448, 15319507986156580901876662272, 229792619792348713528149934080,
    403413710302123297082752106496, 15319507986156580901876662272, 255325133102609681697944371200, 15319507986156580901876662272, 403413710302123297082752106496, 400860458971097200265772662784,
    255325133102609681697944371200, 6186527975076232587541192114176, 395753956309045006631813775360, 229792619792348713528149934080, 403413710302123297082752106496, 15319507986156580901876662272,
    395753956309045006631813775360, 15319507986156580901876662272, 403413710302123297082752106496, 403413710302123297082752106496, 15319507986156580901876662272, 316912650057057350374175801344,
    5189444422733089417503803703296, 5189444866635538807250453790720, 56424801159064186830724662296576, 206124402633871211765214987943936, 56423378489492824555668293812224, 36824198989080874219119784755200,
    1444702608868662622059504131375104, 1444702786278526650506335519506432, 36824455734701814875990762979328, 1137248843888001954420107509760, 227838077753143998511666696290304, 2357104836509491101124846256390144,
    227838430343915075490856931688448, 1137248843888001954420107509760
  ]
def positiveScales : Array ℕ := #[
    6, 9, 10, 6, 11, 6,
    8, 9, 10, 12, 11, 16,
    11, 11, 11, 10, 10, 11,
    16, 11, 8, 12, 6, 10,
    11, 6, 9, 6, 11, 12,
    9, 16, 12, 10, 11, 6,
    12, 6, 11, 11, 6, 0,
    30, 30, 32, 34, 30, 31,
    37, 37, 31, 26, 32, 36,
    30, 26
  ]
def negativeArguments : Array ℕ := #[
    3, 97, 33, 1, 131, 2013,
    37399, 35531
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 7685131763883640746573763182592, 10458117451882892562347801444352, 316912650057057350374175801344, 10378889289368628224754257494016, 318972582282428223151607944052736,
    2963054049870971961660950198616064, 2815055842294326179036210099388416
  ]
def negativeScales : Array ℕ := #[
    1, 6, 5, 0, 7, 10,
    15, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6539158811107971, 9893301530621223, 10891024189919810, 6539158811107971, 11137631598235427, 6539158811107971,
    8184875342908283, 9769837843608060, 10847840355527847, 12214622686302335, 11957464846075818, 16763562518184250,
    11729195859123298, 11957464846075818, 11809366207767696, 10847840355527847, 10847840355527847, 11809366207767696,
    16763562518184250, 11809366207767696, 8184875342908283, 12214622686302335, 6629356620078832, 10536247215688073,
    11348174867535555, 6629356620078832, 9688250309129776, 6629356620078832, 11348174867535555, 12339014868250080,
    9688250309129776, 16286972808809799, 12320518524632690, 10536247215688073, 11348174867535555, 6629356620078832,
    12320518524632690, 6629356620078832, 11348174867535555, 11348174867535555, 6629356620078832, 0,
    30033422939833749, 30033423063241148, 32476100370878593, 34345214349010912, 30476063994955792, 31860425085048832,
    37154399676696352, 37154399853859675, 31860435143769785, 26843390814532202, 32489707915991493, 36860643057643516,
    30489710148632184, 26843390814532202
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 6599912842192769, 5044394119358454, 0, 7033423001537451, 10975131472758174,
    15190712074412934, 15116790672630034
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 668669936861 / 250000000000
noncomputable def negativeCeiling : ℝ := 274578203941 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 147160122170049580178633392128, coefficient := 147160122170049580178633392128 }, { argument := 146928008412683571377089806336, coefficient := 146928008412683571377089806336 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 174317431781872609959232929792, coefficient := 174317431781872609959232929792 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 90060137858011414998911287296, coefficient := 90060137858011414998911287296 }, { argument := 67545103393508561249183465472, coefficient := 67545103393508561249183465472 }, { argument := 71297609137592370207471435776, coefficient := 71297609137592370207471435776 }, { argument := 91936390730053319478055272448, coefficient := 91936390730053319478055272448 }, { argument := 1230821884059489338318454259712, coefficient := 1230821884059489338318454259712 }, { argument := 2152062044232064437578150969344, coefficient := 2152062044232064437578150969344 }, { argument := 65668850521466656770039480320, coefficient := 65668850521466656770039480320 }, { argument := 1230821884059489338318454259712, coefficient := 1230821884059489338318454259712 }, { argument := 69421356265550465728327450624, coefficient := 69421356265550465728327450624 }, { argument := 71297609137592370207471435776, coefficient := 71297609137592370207471435776 }, { argument := 71297609137592370207471435776, coefficient := 71297609137592370207471435776 }, { argument := 69421356265550465728327450624, coefficient := 69421356265550465728327450624 }, { argument := 2152062044232064437578150969344, coefficient := 2152062044232064437578150969344 }, { argument := 69421356265550465728327450624, coefficient := 69421356265550465728327450624 }, { argument := 90060137858011414998911287296, coefficient := 90060137858011414998911287296 }, { argument := 91936390730053319478055272448, coefficient := 91936390730053319478055272448 }, { argument := 7685131763883640746573763182592, coefficient := (-7685131763883640746573763182592) }, { argument := 15319507986156580901876662272, coefficient := 15319507986156580901876662272 }, { argument := 229792619792348713528149934080, coefficient := 229792619792348713528149934080 }, { argument := 403413710302123297082752106496, coefficient := 403413710302123297082752106496 }, { argument := 15319507986156580901876662272, coefficient := 15319507986156580901876662272 }, { argument := 255325133102609681697944371200, coefficient := 255325133102609681697944371200 }, { argument := 15319507986156580901876662272, coefficient := 15319507986156580901876662272 }, { argument := 403413710302123297082752106496, coefficient := 403413710302123297082752106496 }, { argument := 400860458971097200265772662784, coefficient := 400860458971097200265772662784 }, { argument := 255325133102609681697944371200, coefficient := 255325133102609681697944371200 }, { argument := 6186527975076232587541192114176, coefficient := 6186527975076232587541192114176 }, { argument := 395753956309045006631813775360, coefficient := 395753956309045006631813775360 }, { argument := 229792619792348713528149934080, coefficient := 229792619792348713528149934080 }, { argument := 403413710302123297082752106496, coefficient := 403413710302123297082752106496 }, { argument := 15319507986156580901876662272, coefficient := 15319507986156580901876662272 }, { argument := 395753956309045006631813775360, coefficient := 395753956309045006631813775360 }, { argument := 15319507986156580901876662272, coefficient := 15319507986156580901876662272 }, { argument := 403413710302123297082752106496, coefficient := 403413710302123297082752106496 }, { argument := 403413710302123297082752106496, coefficient := 403413710302123297082752106496 }, { argument := 15319507986156580901876662272, coefficient := 15319507986156580901876662272 }, { argument := 10458117451882892562347801444352, coefficient := (-10458117451882892562347801444352) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 5189444422733089417503803703296, coefficient := 5189444422733089417503803703296 }, { argument := 5189444866635538807250453790720, coefficient := 5189444866635538807250453790720 }, { argument := 10378889289368628224754257494016, coefficient := (-10378889289368628224754257494016) }, { argument := 56424801159064186830724662296576, coefficient := 56424801159064186830724662296576 }, { argument := 206124402633871211765214987943936, coefficient := 206124402633871211765214987943936 }, { argument := 56423378489492824555668293812224, coefficient := 56423378489492824555668293812224 }, { argument := 318972582282428223151607944052736, coefficient := (-318972582282428223151607944052736) }, { argument := 36824198989080874219119784755200, coefficient := 36824198989080874219119784755200 }, { argument := 1444702608868662622059504131375104, coefficient := 1444702608868662622059504131375104 }, { argument := 1444702786278526650506335519506432, coefficient := 1444702786278526650506335519506432 }, { argument := 36824455734701814875990762979328, coefficient := 36824455734701814875990762979328 }, { argument := 2963054049870971961660950198616064, coefficient := (-2963054049870971961660950198616064) }, { argument := 1137248843888001954420107509760, coefficient := 1137248843888001954420107509760 }, { argument := 227838077753143998511666696290304, coefficient := 227838077753143998511666696290304 }, { argument := 2357104836509491101124846256390144, coefficient := 2357104836509491101124846256390144 }, { argument := 227838430343915075490856931688448, coefficient := 227838430343915075490856931688448 }, { argument := 1137248843888001954420107509760, coefficient := 1137248843888001954420107509760 }, { argument := 2815055842294326179036210099388416, coefficient := (-2815055842294326179036210099388416) }] }

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

end TermShard13


end Parent3

namespace Parent3

namespace TermShard14

/-! Directed signed-log shard 14.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5775879374046582295177502461526016)
def positiveArguments : Array ℕ := #[
    8529363, 1617812013, 25884993291, 136468725, 23102495, 1044190745,
    2903225
  ]
def positiveCoefficients : Array ℕ := #[
    644460447222855771341212090368, 122238419612401131836245454880768, 122238424726724032784071221313536, 644455332899954823515445657600, 109098448058663564201185771520, 4931051375910684573574910443520,
    109680739457833805804260556800
  ]
def positiveScales : Array ℕ := #[
    23, 30, 34, 27, 24, 29,
    21
  ]
def negativeArguments : Array ℕ := #[
    1551, 65
  ]
def negativeCoefficients : Array ℕ := #[
    245765760119247975215173333942272, 5149830563427181943580356771840
  ]
def negativeScales : Array ℕ := #[
    10, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    23024006569829404, 30591396832786637, 34591396893147431, 27023995120814037, 24461545330993605, 29959738130011458,
    21469224954518289
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10598982971041589, 6022367813028455
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 98136388317 / 1000000000000
noncomputable def negativeCeiling : ℝ := 31728266797 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 644460447222855771341212090368, coefficient := 644460447222855771341212090368 }, { argument := 122238419612401131836245454880768, coefficient := 122238419612401131836245454880768 }, { argument := 122238424726724032784071221313536, coefficient := 122238424726724032784071221313536 }, { argument := 644455332899954823515445657600, coefficient := 644455332899954823515445657600 }, { argument := 245765760119247975215173333942272, coefficient := (-245765760119247975215173333942272) }, { argument := 109098448058663564201185771520, coefficient := 109098448058663564201185771520 }, { argument := 4931051375910684573574910443520, coefficient := 4931051375910684573574910443520 }, { argument := 109680739457833805804260556800, coefficient := 109680739457833805804260556800 }, { argument := 5149830563427181943580356771840, coefficient := (-5149830563427181943580356771840) }] }

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

end TermShard14


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
