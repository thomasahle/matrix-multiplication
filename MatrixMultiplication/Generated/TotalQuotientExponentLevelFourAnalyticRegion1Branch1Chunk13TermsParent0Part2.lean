import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-186974209366325815023003850768384)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1561091475, 89577, 93351, 55611, 2775, 22707,
    103443, 2523, 1082367, 47937, 2523, 47937,
    93351, 1763577, 93351, 1082367, 1763577, 22707,
    93351, 93351, 103443, 2021990037, 1050597, 27261,
    238269728709, 1692279, 64707954075, 1692279, 1763577, 1050597,
    52425, 198029846871, 198029891241, 12542967, 55611, 1443,
    1478854599, 89577, 401403225, 89577, 93351, 55611,
    2775, 6452149547, 6452150997, 673, 13527, 61623,
    1503, 644787, 28557, 1503, 28557, 55611,
    1050597, 55611, 644787, 1050597, 13527, 55611,
    55611, 61623, 550549941, 644787
  ]
def negativeCoefficients : Array ℕ := #[
    7199263728743688163452518400, 423015422436014209307246592, 440837633542364250343735296, 262615522478863839978848256, 13104566989963265468006400, 428923102906084135469580288,
    488495756087484709840355328, 381264980360963675972960256, 5111333642964169281012498432, 452752164178644365217890304, 381264980360963675972960256, 452752164178644365217890304,
    440837633542364250343735296, 16656513829519600594068701184, 440837633542364250343735296, 5111333642964169281012498432, 16656513829519600594068701184, 428923102906084135469580288,
    440837633542364250343735296, 440837633542364250343735296, 488495756087484709840355328, 298393061857036055994313998336, 9922608119606801305146753024, 514945730758037592682266624,
    1098825176501782090701588135936, 15983123258528320665176506368, 298412767088719020214242508800, 15983123258528320665176506368, 16656513829519600594068701184, 9922608119606801305146753024,
    495140125728882300656025600, 228312869011576827715409412096, 228312920166703987121209737216, 7404060869567503152137109504, 262615522478863839978848256, 13628749669561796086726656,
    27280052309981365397549481984, 423015422436014209307246592, 7404582561936651731966361600, 423015422436014209307246592, 440837633542364250343735296, 262615522478863839978848256,
    13104566989963265468006400, 238042302837620036137495035904, 238042356333177849895194722304, 26035426451220653906472206336, 255517805655110763222663168, 291006389773876147003588608,
    227126938360098456197922816, 3044920517390069928403402752, 269713239302616916735033344, 227126938360098456197922816, 269713239302616916735033344, 262615522478863839978848256,
    9922608119606801305146753024, 262615522478863839978848256, 3044920517390069928403402752, 9922608119606801305146753024, 255517805655110763222663168, 262615522478863839978848256,
    262615522478863839978848256, 291006389773876147003588608, 81246830891383146346602037248, 3044920517390069928403402752
  ]
def negativeScales : Array ℕ := #[
    30, 16, 16, 15, 11, 14,
    16, 11, 20, 15, 11, 15,
    16, 20, 16, 20, 20, 14,
    16, 16, 16, 30, 20, 14,
    37, 20, 35, 20, 20, 20,
    15, 37, 37, 23, 15, 10,
    30, 16, 28, 16, 16, 15,
    11, 32, 32, 9, 13, 15,
    10, 19, 14, 10, 14, 15,
    20, 15, 19, 20, 13, 15,
    15, 15, 29, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30539907931125137, 16450840729627935, 16510377856605633, 15763082659843835, 11438272056124861, 14470849492418713,
    16658476495620780, 11300924490976301, 20045758328475847, 15548852004421171, 11300924490976301, 15548852004421171,
    16510377856605633, 20750073136576977, 16510377856605633, 20045758328475847, 20750073136576977, 14470849492418713,
    16510377856605633, 16510377856605633, 16658476495620780, 30913128748135173, 20002777939291802, 14734550864397523,
    37793804718411799, 20690536009432220, 35913224017455375, 20690536009432220, 20750073136576977, 20002777939291802,
    15677967335914047, 37526926932084899, 37526927255330979, 23580375317767797, 15763082659843835, 10494855584491427,
    30461833067604137, 16450840729627935, 28580476966915837, 16450840729627935, 16510377856605633, 15763082659843835,
    11438272056124861, 32587132731450740, 32587133055669445, 9394462694610323, 13723554295483443, 15911181303864252,
    10553629293917849, 19298463131415911, 14801556808026795, 10553629293917849, 14801556808026795, 15763082659843835,
    20002777939291802, 15763082659843835, 19298463131415911, 20002777939291802, 13723554295483443, 15763082659843835,
    15763082659843835, 15911181303864252, 29036298197302870, 19298463131415911
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
noncomputable def negativeCeiling : ℝ := 1218438857 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7199263728743688163452518400, coefficient := (-7199263728743688163452518400) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 488495756087484709840355328, coefficient := (-488495756087484709840355328) }, { argument := 381264980360963675972960256, coefficient := (-381264980360963675972960256) }, { argument := 5111333642964169281012498432, coefficient := (-5111333642964169281012498432) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 381264980360963675972960256, coefficient := (-381264980360963675972960256) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 16656513829519600594068701184, coefficient := (-16656513829519600594068701184) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 5111333642964169281012498432, coefficient := (-5111333642964169281012498432) }, { argument := 16656513829519600594068701184, coefficient := (-16656513829519600594068701184) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 488495756087484709840355328, coefficient := (-488495756087484709840355328) }, { argument := 298393061857036055994313998336, coefficient := (-298393061857036055994313998336) }, { argument := 9922608119606801305146753024, coefficient := (-9922608119606801305146753024) }, { argument := 514945730758037592682266624, coefficient := (-514945730758037592682266624) }, { argument := 1098825176501782090701588135936, coefficient := (-1098825176501782090701588135936) }, { argument := 15983123258528320665176506368, coefficient := (-15983123258528320665176506368) }, { argument := 298412767088719020214242508800, coefficient := (-298412767088719020214242508800) }, { argument := 15983123258528320665176506368, coefficient := (-15983123258528320665176506368) }, { argument := 16656513829519600594068701184, coefficient := (-16656513829519600594068701184) }, { argument := 9922608119606801305146753024, coefficient := (-9922608119606801305146753024) }, { argument := 495140125728882300656025600, coefficient := (-495140125728882300656025600) }, { argument := 228312869011576827715409412096, coefficient := (-228312869011576827715409412096) }, { argument := 228312920166703987121209737216, coefficient := (-228312920166703987121209737216) }, { argument := 7404060869567503152137109504, coefficient := (-7404060869567503152137109504) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 27280052309981365397549481984, coefficient := (-27280052309981365397549481984) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 7404582561936651731966361600, coefficient := (-7404582561936651731966361600) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 238042302837620036137495035904, coefficient := (-238042302837620036137495035904) }, { argument := 238042356333177849895194722304, coefficient := (-238042356333177849895194722304) }, { argument := 26035426451220653906472206336, coefficient := (-26035426451220653906472206336) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 291006389773876147003588608, coefficient := (-291006389773876147003588608) }, { argument := 227126938360098456197922816, coefficient := (-227126938360098456197922816) }, { argument := 3044920517390069928403402752, coefficient := (-3044920517390069928403402752) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 227126938360098456197922816, coefficient := (-227126938360098456197922816) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 9922608119606801305146753024, coefficient := (-9922608119606801305146753024) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 3044920517390069928403402752, coefficient := (-3044920517390069928403402752) }, { argument := 9922608119606801305146753024, coefficient := (-9922608119606801305146753024) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 291006389773876147003588608, coefficient := (-291006389773876147003588608) }, { argument := 81246830891383146346602037248, coefficient := (-81246830891383146346602037248) }, { argument := 3044920517390069928403402752, coefficient := (-3044920517390069928403402752) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4093814205067360690425538304540672)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    16731, 64943414757, 1038609, 17618910075, 1038609, 1082367,
    644787, 32175, 3884973645, 3884974515, 2021990037, 1050597,
    27261, 238269728709, 1692279, 64707954075, 1692279, 1763577,
    1050597, 52425, 3164199359421, 3164200070211, 9015, 202668746515,
    202668792045, 8133, 9163613275946693, 13527, 351, 33497142218112671,
    21789, 2290848861212839, 21789, 22707, 13527, 675,
    50892251805763187, 50892254785321357, 180961841, 198029846871, 198029891241, 9015,
    531, 675, 3075, 75, 32175, 1425,
    75, 1425, 2775, 52425, 2775, 32175,
    52425, 675, 2775, 2775, 3075, 48780573,
    55611, 1443, 5752803021, 89577
  ]
def negativeCoefficients : Array ℕ := #[
    158019827249784068140695552, 299498637823787797537596899328, 4904692330406759345751588864, 81252881252806940397718732800, 4904692330406759345751588864, 5111333642964169281012498432,
    3044920517390069928403402752, 151942141586330834750668800, 143330229124843090825854320640, 143330261222177779080474132480, 298393061857036055994313998336, 9922608119606801305146753024,
    514945730758037592682266624, 1098825176501782090701588135936, 15983123258528320665176506368, 298412767088719020214242508800, 15983123258528320665176506368, 16656513829519600594068701184,
    9922608119606801305146753024, 495140125728882300656025600, 3648073486339680701909770960896, 3648074305824756961410533031936, 348750920442428224319237652480, 233661156168857474512338288640,
    233661208661373579262081105920, 629260396219249860984661082112, 5158655666865107091371082121216, 255517805655110763222663168, 13260405083897963760058368, 18857214651433591870351948644352,
    411582573180986798244888576, 5158533038860133413847482499072, 411582573180986798244888576, 428923102906084135469580288, 255517805655110763222663168, 12750389503748042076979200,
    14324895391780033821784955420672, 14324896230451100330579766280192, 6836545060934287687098132594688, 228312869011576827715409412096, 228312920166703987121209737216, 348750920442428224319237652480,
    20542067526891778936607342592, 12750389503748042076979200, 14521276934824159032115200, 11333679558887148512870400, 151942141586330834750668800, 13458744476178488859033600,
    11333679558887148512870400, 13458744476178488859033600, 13104566989963265468006400, 495140125728882300656025600, 13104566989963265468006400, 151942141586330834750668800,
    495140125728882300656025600, 12750389503748042076979200, 13104566989963265468006400, 13104566989963265468006400, 14521276934824159032115200, 7198741967199249307212447744,
    262615522478863839978848256, 13628749669561796086726656, 26530121258712538803270057984, 423015422436014209307246592
  ]
def negativeScales : Array ℕ := #[
    14, 35, 19, 34, 19, 20,
    19, 14, 31, 31, 30, 20,
    14, 37, 20, 35, 20, 20,
    20, 15, 41, 41, 13, 37,
    37, 12, 53, 13, 8, 54,
    14, 51, 14, 14, 13, 9,
    55, 55, 27, 37, 37, 13,
    9, 9, 11, 6, 14, 10,
    6, 10, 11, 15, 11, 14,
    15, 9, 11, 11, 11, 25,
    15, 10, 32, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14030236056361794, 35918464199172762, 19986221220472518, 34036405629203032, 19986221220472518, 20045758328475847,
    19298463131415911, 14973652543452428, 31855257667569159, 31855257990645892, 30913128748135173, 20002777939291802,
    14734550864397523, 37793804718411799, 20690536009432220, 35913224017455375, 20690536009432220, 20750073136576977,
    20002777939291802, 15677967335914047, 41524977637886750, 41524977961966550, 13138111776319705, 37560332672161885,
    37560332996266607, 12989571918588865, 53024837998425466, 13723554295483443, 8455327220304618, 54894887540629075,
    14411312365441260, 51024803703266250, 14411312365441260, 14470849492418713, 13723554295483443, 9398743691938200,
    55498295545180985, 55498295629645585, 27431110270750058, 37526926932084899, 37526927255330979, 13138111776319705,
    9052568050804154, 9398743691938200, 11586370695117825, 6228818690495881, 14973652543452428, 10476746203939589,
    6228818690495881, 10476746203939589, 11438272056124861, 15677967335914047, 11438272056124861, 14973652543452428,
    15677967335914047, 9398743691938200, 11438272056124861, 11438272056124861, 11586370695117825, 25539803369033840,
    15763082659843835, 10494855584491427, 32421617926417424, 16450840729627935
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
noncomputable def negativeCeiling : ℝ := 45640398427 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 158019827249784068140695552, coefficient := (-158019827249784068140695552) }, { argument := 299498637823787797537596899328, coefficient := (-299498637823787797537596899328) }, { argument := 4904692330406759345751588864, coefficient := (-4904692330406759345751588864) }, { argument := 81252881252806940397718732800, coefficient := (-81252881252806940397718732800) }, { argument := 4904692330406759345751588864, coefficient := (-4904692330406759345751588864) }, { argument := 5111333642964169281012498432, coefficient := (-5111333642964169281012498432) }, { argument := 3044920517390069928403402752, coefficient := (-3044920517390069928403402752) }, { argument := 151942141586330834750668800, coefficient := (-151942141586330834750668800) }, { argument := 143330229124843090825854320640, coefficient := (-143330229124843090825854320640) }, { argument := 143330261222177779080474132480, coefficient := (-143330261222177779080474132480) }, { argument := 298393061857036055994313998336, coefficient := (-298393061857036055994313998336) }, { argument := 9922608119606801305146753024, coefficient := (-9922608119606801305146753024) }, { argument := 514945730758037592682266624, coefficient := (-514945730758037592682266624) }, { argument := 1098825176501782090701588135936, coefficient := (-1098825176501782090701588135936) }, { argument := 15983123258528320665176506368, coefficient := (-15983123258528320665176506368) }, { argument := 298412767088719020214242508800, coefficient := (-298412767088719020214242508800) }, { argument := 15983123258528320665176506368, coefficient := (-15983123258528320665176506368) }, { argument := 16656513829519600594068701184, coefficient := (-16656513829519600594068701184) }, { argument := 9922608119606801305146753024, coefficient := (-9922608119606801305146753024) }, { argument := 495140125728882300656025600, coefficient := (-495140125728882300656025600) }, { argument := 3648073486339680701909770960896, coefficient := (-3648073486339680701909770960896) }, { argument := 3648074305824756961410533031936, coefficient := (-3648074305824756961410533031936) }, { argument := 348750920442428224319237652480, coefficient := (-348750920442428224319237652480) }, { argument := 233661156168857474512338288640, coefficient := (-233661156168857474512338288640) }, { argument := 233661208661373579262081105920, coefficient := (-233661208661373579262081105920) }, { argument := 629260396219249860984661082112, coefficient := (-629260396219249860984661082112) }, { argument := 5158655666865107091371082121216, coefficient := (-5158655666865107091371082121216) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 18857214651433591870351948644352, coefficient := (-18857214651433591870351948644352) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 5158533038860133413847482499072, coefficient := (-5158533038860133413847482499072) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 14324895391780033821784955420672, coefficient := (-14324895391780033821784955420672) }, { argument := 14324896230451100330579766280192, coefficient := (-14324896230451100330579766280192) }, { argument := 6836545060934287687098132594688, coefficient := (-6836545060934287687098132594688) }, { argument := 228312869011576827715409412096, coefficient := (-228312869011576827715409412096) }, { argument := 228312920166703987121209737216, coefficient := (-228312920166703987121209737216) }, { argument := 348750920442428224319237652480, coefficient := (-348750920442428224319237652480) }, { argument := 20542067526891778936607342592, coefficient := (-20542067526891778936607342592) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 14521276934824159032115200, coefficient := (-14521276934824159032115200) }, { argument := 11333679558887148512870400, coefficient := (-11333679558887148512870400) }, { argument := 151942141586330834750668800, coefficient := (-151942141586330834750668800) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 11333679558887148512870400, coefficient := (-11333679558887148512870400) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 495140125728882300656025600, coefficient := (-495140125728882300656025600) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 151942141586330834750668800, coefficient := (-151942141586330834750668800) }, { argument := 495140125728882300656025600, coefficient := (-495140125728882300656025600) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 14521276934824159032115200, coefficient := (-14521276934824159032115200) }, { argument := 7198741967199249307212447744, coefficient := (-7198741967199249307212447744) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 26530121258712538803270057984, coefficient := (-26530121258712538803270057984) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
