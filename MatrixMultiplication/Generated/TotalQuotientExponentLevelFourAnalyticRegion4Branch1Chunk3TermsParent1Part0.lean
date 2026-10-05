import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 3, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3

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
def constantNumerator : ℤ := 5107600303073544000528537616384
def positiveArguments : Array ℕ := #[
    9, 25165841, 25165807, 47522589, 78336265, 47463121,
    1702043, 122425075, 122422981, 1703049, 102605, 967407,
    21193603, 1934813, 102583
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 237684648103253430348569116672, 237684326982332595212694585344, 448838162945579380132584357888, 1479730208916777951664285941760, 448276503565572796009448210432,
    32150683262411598193819123712, 1156272141685605061020247654400, 1156252364414774802946092695552, 32169686065138665646159036416, 969076825949679894302556160, 36547603136747798937968050176,
    400335841833782245639692746752, 36547584247281867459387195392, 968869041824433629913153536
  ]
def positiveScales : Array ℕ := #[
    3, 24, 24, 25, 26, 25,
    20, 26, 26, 20, 16, 19,
    24, 20, 16
  ]
def negativeArguments : Array ℕ := #[
    860714238431, 8115203885621, 177784946021969, 16230399382543, 860529688717, 2695040385847,
    193934167955147, 387861849694645, 10786393383897, 2695040385847, 35564015285177, 10766909276011,
    860714238431, 860712009249, 860712009249, 8115192313291, 177784709327279, 16230376238065,
    860527460211, 35564015285177, 639350428372925, 1278678698212717, 1112040838523, 193934167955147,
    639350428372925, 24211420902191, 8115203885621, 8115192313291, 10766909276011, 24211420902191,
    193688123846767, 10773141646535, 387861849694645, 1278678698212717, 193688123846767, 177784946021969,
    177784709327279, 10786393383897, 1112040838523, 10773141646535, 16230399382543, 16230376238065,
    860529688717, 860527460211, 3, 15, 15, 3
  ]
def negativeCoefficients : Array ℕ := #[
    242269520216895740482420736, 9136907298829584210543509504, 100084027082077916695864803328, 9136902576411872895136956416, 242217574090445632256868352, 3034345719362246740465942528,
    109175230817150901927609892864, 109173405109752159360117637120, 3036099826524382038098706432, 3034345719362246740465942528, 10010380374132610077254746112, 3030615537710942279188873216,
    242269520216895740482420736, 242268892757944206668857344, 242268892757944206668857344, 9136894269544315258440515584, 100083893834813206123981570048, 9136889547229060834556641280,
    242216946821771182699708416, 10010380374132610077254746112, 359922293872434002901178777600, 359916056799836449426848612352, 10016373411985913426860834816, 109175230817150901927609892864,
    359922293872434002901178777600, 109038546153217625681335156736, 9136907298829584210543509504, 9136894269544315258440515584, 3030615537710942279188873216, 109038546153217625681335156736,
    109036720297798792686080098304, 3032369794059037358119976960, 109173405109752159360117637120, 359916056799836449426848612352, 109036720297798792686080098304, 100084027082077916695864803328,
    100083893834813206123981570048, 3036099826524382038098706432, 10016373411985913426860834816, 3032369794059037358119976960, 9136902576411872895136956416, 9136889547229060834556641280,
    242217574090445632256868352, 242216946821771182699708416, 475368975085586025561263702016, 2376844875427930127806318510080, 2376844875427930127806318510080, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    39, 42, 47, 43, 39, 41,
    47, 48, 43, 41, 45, 43,
    39, 39, 39, 42, 47, 43,
    39, 45, 49, 50, 40, 47,
    49, 44, 42, 42, 43, 44,
    47, 43, 48, 50, 47, 47,
    47, 43, 40, 43, 43, 43,
    39, 39, 1, 3, 3, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 24584963475288950, 24584961526152240, 25502110099586624, 26223177007786968, 25500303634174068,
    20698836054700387, 26867323838820497, 26867299162264296, 20699688514048451, 16646741510443359, 19883763451164180,
    24337125536884525, 20883762705513483, 16646432142536656
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39646743378698587, 42883764483266852, 47337126497253716, 43883763737608550, 39646434010625719, 41293444030930261,
    47462560332986002, 48462536206991359, 43294277789096875, 41293444030930261, 45015483451544399, 43291669406156777,
    39646743378698587, 39646739642227364, 39646739642227364, 42883762425973377, 47337124576514697, 43883761680330190,
    39646430274486500, 45015483451544399, 49183600218439254, 50183575217843778, 40016346909131310, 47462560332986002,
    49183600218439254, 44460752983190309, 42883764483266852, 42883762425973377, 43291669406156777, 44460752983190309,
    47460728824993911, 43292504261221066, 48462536206991359, 50183575217843778, 47460728824993911, 47337126497253716,
    47337124576514697, 43294277789096875, 40016346909131310, 43292504261221066, 43883763737608550, 43883761680330190,
    39646434010625719, 39646430274486500, 1584962500724866, 3906890600547867, 3906890600547867, 1584962500724866
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 118216669 / 62500000000
noncomputable def negativeCeiling : ℝ := 237037273 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 242269520216895740482420736, coefficient := (-242269520216895740482420736) }, { argument := 9136907298829584210543509504, coefficient := (-9136907298829584210543509504) }, { argument := 100084027082077916695864803328, coefficient := (-100084027082077916695864803328) }, { argument := 9136902576411872895136956416, coefficient := (-9136902576411872895136956416) }, { argument := 242217574090445632256868352, coefficient := (-242217574090445632256868352) }, { argument := 3034345719362246740465942528, coefficient := (-3034345719362246740465942528) }, { argument := 109175230817150901927609892864, coefficient := (-109175230817150901927609892864) }, { argument := 109173405109752159360117637120, coefficient := (-109173405109752159360117637120) }, { argument := 3036099826524382038098706432, coefficient := (-3036099826524382038098706432) }, { argument := 3034345719362246740465942528, coefficient := (-3034345719362246740465942528) }, { argument := 10010380374132610077254746112, coefficient := (-10010380374132610077254746112) }, { argument := 3030615537710942279188873216, coefficient := (-3030615537710942279188873216) }, { argument := 242269520216895740482420736, coefficient := (-242269520216895740482420736) }, { argument := 242268892757944206668857344, coefficient := (-242268892757944206668857344) }, { argument := 242268892757944206668857344, coefficient := (-242268892757944206668857344) }, { argument := 9136894269544315258440515584, coefficient := (-9136894269544315258440515584) }, { argument := 100083893834813206123981570048, coefficient := (-100083893834813206123981570048) }, { argument := 9136889547229060834556641280, coefficient := (-9136889547229060834556641280) }, { argument := 242216946821771182699708416, coefficient := (-242216946821771182699708416) }, { argument := 10010380374132610077254746112, coefficient := (-10010380374132610077254746112) }, { argument := 359922293872434002901178777600, coefficient := (-359922293872434002901178777600) }, { argument := 359916056799836449426848612352, coefficient := (-359916056799836449426848612352) }, { argument := 10016373411985913426860834816, coefficient := (-10016373411985913426860834816) }, { argument := 109175230817150901927609892864, coefficient := (-109175230817150901927609892864) }, { argument := 359922293872434002901178777600, coefficient := (-359922293872434002901178777600) }, { argument := 109038546153217625681335156736, coefficient := (-109038546153217625681335156736) }, { argument := 9136907298829584210543509504, coefficient := (-9136907298829584210543509504) }, { argument := 9136894269544315258440515584, coefficient := (-9136894269544315258440515584) }, { argument := 3030615537710942279188873216, coefficient := (-3030615537710942279188873216) }, { argument := 109038546153217625681335156736, coefficient := (-109038546153217625681335156736) }, { argument := 109036720297798792686080098304, coefficient := (-109036720297798792686080098304) }, { argument := 3032369794059037358119976960, coefficient := (-3032369794059037358119976960) }, { argument := 109173405109752159360117637120, coefficient := (-109173405109752159360117637120) }, { argument := 359916056799836449426848612352, coefficient := (-359916056799836449426848612352) }, { argument := 109036720297798792686080098304, coefficient := (-109036720297798792686080098304) }, { argument := 100084027082077916695864803328, coefficient := (-100084027082077916695864803328) }, { argument := 100083893834813206123981570048, coefficient := (-100083893834813206123981570048) }, { argument := 3036099826524382038098706432, coefficient := (-3036099826524382038098706432) }, { argument := 10016373411985913426860834816, coefficient := (-10016373411985913426860834816) }, { argument := 3032369794059037358119976960, coefficient := (-3032369794059037358119976960) }, { argument := 9136902576411872895136956416, coefficient := (-9136902576411872895136956416) }, { argument := 9136889547229060834556641280, coefficient := (-9136889547229060834556641280) }, { argument := 242217574090445632256868352, coefficient := (-242217574090445632256868352) }, { argument := 242216946821771182699708416, coefficient := (-242216946821771182699708416) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 237684648103253430348569116672, coefficient := 237684648103253430348569116672 }, { argument := 237684326982332595212694585344, coefficient := 237684326982332595212694585344 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 448838162945579380132584357888, coefficient := 448838162945579380132584357888 }, { argument := 1479730208916777951664285941760, coefficient := 1479730208916777951664285941760 }, { argument := 448276503565572796009448210432, coefficient := 448276503565572796009448210432 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 32150683262411598193819123712, coefficient := 32150683262411598193819123712 }, { argument := 1156272141685605061020247654400, coefficient := 1156272141685605061020247654400 }, { argument := 1156252364414774802946092695552, coefficient := 1156252364414774802946092695552 }, { argument := 32169686065138665646159036416, coefficient := 32169686065138665646159036416 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 969076825949679894302556160, coefficient := 969076825949679894302556160 }, { argument := 36547603136747798937968050176, coefficient := 36547603136747798937968050176 }, { argument := 400335841833782245639692746752, coefficient := 400335841833782245639692746752 }, { argument := 36547584247281867459387195392, coefficient := 36547584247281867459387195392 }, { argument := 968869041824433629913153536, coefficient := 968869041824433629913153536 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3
