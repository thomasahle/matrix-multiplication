import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 5, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 271844063033978256015680050561024
def positiveArguments : Array ℕ := #[
    17, 2097153
  ]
def positiveCoefficients : Array ℕ := #[
    5387515050969974956360988622848, 158456400586392401101411319808
  ]
def positiveScales : Array ℕ := #[
    4, 21
  ]
def negativeArguments : Array ℕ := #[
    2524712606237, 69106257850595, 138251531116627, 1243175752165, 359822655117, 934468857357,
    661939325364465, 14951559231171, 1439047925391, 910012740423, 64239259224369, 32119927060221,
    1819423908423, 359822655117, 607568411655, 359663241573, 2524709316067, 69106192387869,
    138251400191917, 1243174104603, 607568411655, 50578200373659, 2239201781248425, 3161149214565,
    4859723984499, 64239259224369, 141389940207715, 282782371922853, 64219048629111, 934468857357,
    50578200373659, 14946085795221, 2524712606237, 2524709316067, 359663241573, 14946085795221,
    330850179928755, 14946143212269, 719205173631, 32119927060221, 282782371922853, 565569726168467,
    32109823115081, 661939325364465, 2239201781248425, 330850179928755, 69106257850595, 69106192387869,
    1819423908423, 64219048629111, 32109823115081, 113676230843, 14951559231171, 3161149214565,
    14946143212269, 138251531116627, 138251400191917, 1439047925391, 4859723984499, 719205173631,
    1243175752165, 1243174104603
  ]
def negativeCoefficients : Array ℕ := #[
    710643422041659187209961472, 38903364638113631979584880640, 38914346501265118123169677312, 699845731775791260741140480, 405124293876095923947307008, 16833894391129273518457356288,
    186319356190830130334049239040, 16833959145527403815532232704, 405055981284949558082666496, 512291629833928337812094976, 18081743994089057893497176064, 18081911442447350829208829952,
    512122302250174639912255488, 405124293876095923947307008, 1368122436165771059464765440, 404944810181756871405207552, 710642495941135063110909952, 38903327785875079447474864128,
    38914309649235420023778967552, 699844804280840102017499136, 1368122436165771059464765440, 56945991088970238487708041216, 630279269227359857967680716800, 56946201699109880426617896960,
    1367890695357072404952121344, 18081743994089057893497176064, 636763682033401983809502576640, 636769292409352890621880172544, 18076055217259503848905506816, 16833894391129273518457356288,
    56945991088970238487708041216, 16827796604501189746338299904, 710643422041659187209961472, 710642495941135063110909952, 404944810181756871405207552, 16827796604501189746338299904,
    186252093380325321604658626560, 16827861250350184124808953856, 404876518995938059455823872, 18081911442447350829208829952, 636769292409352890621880172544, 636774902006085360407080337408,
    18076223427001416337454006272, 186319356190830130334049239040, 630279269227359857967680716800, 186252093380325321604658626560, 38903364638113631979584880640, 38903327785875079447474864128,
    512122302250174639912255488, 18076055217259503848905506816, 18076223427001416337454006272, 511952230865417284383408128, 16833959145527403815532232704, 56946201699109880426617896960,
    16827861250350184124808953856, 38914346501265118123169677312, 38914309649235420023778967552, 405055981284949558082666496, 1367890695357072404952121344, 404876518995938059455823872,
    699845731775791260741140480, 699844804280840102017499136
  ]
def negativeScales : Array ℕ := #[
    41, 45, 46, 40, 38, 39,
    49, 43, 40, 39, 45, 44,
    40, 38, 39, 38, 41, 45,
    46, 40, 39, 45, 50, 41,
    42, 45, 47, 48, 45, 39,
    45, 43, 41, 41, 38, 43,
    48, 43, 39, 44, 48, 49,
    44, 49, 50, 48, 45, 45,
    40, 45, 44, 36, 43, 41,
    43, 46, 46, 40, 42, 39,
    40, 40
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 21000000687930439
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41199256310610039, 45973881607439322, 46974288802239363, 40177167408371744, 38388495068026840, 39765355628766846,
    49233692311305287, 43765361178324651, 40388251778379506, 39727095787467302, 45868520492491681, 44868533852696797,
    40726618855124460, 38388495068026840, 39144255907785732, 38387855763950969, 41199254430508905, 45973880240807386,
    46974287436000840, 40177165496388585, 39144255907785732, 45523580938821614, 50991905983772265, 41523586274502605,
    42144011514721657, 45868520492491681, 47006672805510046, 48006685516702805, 45868066528437351, 39765355628766846,
    45523580938821614, 43764832942804055, 41199256310610039, 41199254430508905, 38387855763950969, 43764832942804055,
    48233171392569740, 43764838485066624, 39387612442734792, 44868533852696797, 48006685516702805, 49006698226018152,
    44868079953614442, 49233692311305287, 50991905983772265, 48233171392569740, 45973881607439322, 45973880240807386,
    40726618855124460, 45868066528437351, 44868079953614442, 36726139669013594, 43765361178324651, 41523586274502605,
    43764838485066624, 46974288802239363, 46974287436000840, 40388251778379506, 42144011514721657, 39387612442734792,
    40177167408371744, 40177165496388585
  ]

abbrev PositiveTerm := Fin 2
abbrev NegativeTerm := Fin 62
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
noncomputable def positiveFloor : ℝ := 76281427 / 250000000000
noncomputable def negativeCeiling : ℝ := 1566190503 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 710643422041659187209961472, coefficient := (-710643422041659187209961472) }, { argument := 38903364638113631979584880640, coefficient := (-38903364638113631979584880640) }, { argument := 38914346501265118123169677312, coefficient := (-38914346501265118123169677312) }, { argument := 699845731775791260741140480, coefficient := (-699845731775791260741140480) }, { argument := 405124293876095923947307008, coefficient := (-405124293876095923947307008) }, { argument := 16833894391129273518457356288, coefficient := (-16833894391129273518457356288) }, { argument := 186319356190830130334049239040, coefficient := (-186319356190830130334049239040) }, { argument := 16833959145527403815532232704, coefficient := (-16833959145527403815532232704) }, { argument := 405055981284949558082666496, coefficient := (-405055981284949558082666496) }, { argument := 512291629833928337812094976, coefficient := (-512291629833928337812094976) }, { argument := 18081743994089057893497176064, coefficient := (-18081743994089057893497176064) }, { argument := 18081911442447350829208829952, coefficient := (-18081911442447350829208829952) }, { argument := 512122302250174639912255488, coefficient := (-512122302250174639912255488) }, { argument := 405124293876095923947307008, coefficient := (-405124293876095923947307008) }, { argument := 1368122436165771059464765440, coefficient := (-1368122436165771059464765440) }, { argument := 404944810181756871405207552, coefficient := (-404944810181756871405207552) }, { argument := 710642495941135063110909952, coefficient := (-710642495941135063110909952) }, { argument := 38903327785875079447474864128, coefficient := (-38903327785875079447474864128) }, { argument := 38914309649235420023778967552, coefficient := (-38914309649235420023778967552) }, { argument := 699844804280840102017499136, coefficient := (-699844804280840102017499136) }, { argument := 1368122436165771059464765440, coefficient := (-1368122436165771059464765440) }, { argument := 56945991088970238487708041216, coefficient := (-56945991088970238487708041216) }, { argument := 630279269227359857967680716800, coefficient := (-630279269227359857967680716800) }, { argument := 56946201699109880426617896960, coefficient := (-56946201699109880426617896960) }, { argument := 1367890695357072404952121344, coefficient := (-1367890695357072404952121344) }, { argument := 18081743994089057893497176064, coefficient := (-18081743994089057893497176064) }, { argument := 636763682033401983809502576640, coefficient := (-636763682033401983809502576640) }, { argument := 636769292409352890621880172544, coefficient := (-636769292409352890621880172544) }, { argument := 18076055217259503848905506816, coefficient := (-18076055217259503848905506816) }, { argument := 16833894391129273518457356288, coefficient := (-16833894391129273518457356288) }, { argument := 56945991088970238487708041216, coefficient := (-56945991088970238487708041216) }, { argument := 16827796604501189746338299904, coefficient := (-16827796604501189746338299904) }, { argument := 710643422041659187209961472, coefficient := (-710643422041659187209961472) }, { argument := 710642495941135063110909952, coefficient := (-710642495941135063110909952) }, { argument := 404944810181756871405207552, coefficient := (-404944810181756871405207552) }, { argument := 16827796604501189746338299904, coefficient := (-16827796604501189746338299904) }, { argument := 186252093380325321604658626560, coefficient := (-186252093380325321604658626560) }, { argument := 16827861250350184124808953856, coefficient := (-16827861250350184124808953856) }, { argument := 404876518995938059455823872, coefficient := (-404876518995938059455823872) }, { argument := 18081911442447350829208829952, coefficient := (-18081911442447350829208829952) }, { argument := 636769292409352890621880172544, coefficient := (-636769292409352890621880172544) }, { argument := 636774902006085360407080337408, coefficient := (-636774902006085360407080337408) }, { argument := 18076223427001416337454006272, coefficient := (-18076223427001416337454006272) }, { argument := 186319356190830130334049239040, coefficient := (-186319356190830130334049239040) }, { argument := 630279269227359857967680716800, coefficient := (-630279269227359857967680716800) }, { argument := 186252093380325321604658626560, coefficient := (-186252093380325321604658626560) }, { argument := 38903364638113631979584880640, coefficient := (-38903364638113631979584880640) }, { argument := 38903327785875079447474864128, coefficient := (-38903327785875079447474864128) }, { argument := 512122302250174639912255488, coefficient := (-512122302250174639912255488) }, { argument := 18076055217259503848905506816, coefficient := (-18076055217259503848905506816) }, { argument := 18076223427001416337454006272, coefficient := (-18076223427001416337454006272) }, { argument := 511952230865417284383408128, coefficient := (-511952230865417284383408128) }, { argument := 16833959145527403815532232704, coefficient := (-16833959145527403815532232704) }, { argument := 56946201699109880426617896960, coefficient := (-56946201699109880426617896960) }, { argument := 16827861250350184124808953856, coefficient := (-16827861250350184124808953856) }, { argument := 38914346501265118123169677312, coefficient := (-38914346501265118123169677312) }, { argument := 38914309649235420023778967552, coefficient := (-38914309649235420023778967552) }, { argument := 405055981284949558082666496, coefficient := (-405055981284949558082666496) }, { argument := 1367890695357072404952121344, coefficient := (-1367890695357072404952121344) }, { argument := 404876518995938059455823872, coefficient := (-404876518995938059455823872) }, { argument := 699845731775791260741140480, coefficient := (-699845731775791260741140480) }, { argument := 699844804280840102017499136, coefficient := (-699844804280840102017499136) }, { argument := 5387515050969974956360988622848, coefficient := 5387515050969974956360988622848 }, { argument := 158456400586392401101411319808, coefficient := 158456400586392401101411319808 }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-254699928293615386219747813097472)
def positiveArguments : Array ℕ := #[
    2097151, 23377833, 79081905, 11684691, 123045, 277337809,
    8666883, 7872399, 230625, 19186923, 53090475, 19186995,
    115293, 300969, 1029763, 16480859, 74099
  ]
def positiveCoefficients : Array ℕ := #[
    158456249470664949272764481536, 441594780005295706300137603072, 1493814950293925640692847083520, 441435145128708780813333823488, 74376138737241023400860712960, 2619381547308206872347570864128,
    2619404658569774036391246692352, 74352706354753024221310353408, 4356383080447247709634560000, 181215364169201403505007394816, 2005701437597030619812777164800, 181216044189974936733918167040,
    4355646391275920044981223424, 2842571835965588500641742848, 155613384847977422854119489536, 155657312301001076293897289728, 2799381072113262725517279232
  ]
def positiveScales : Array ℕ := #[
    20, 24, 26, 23, 16, 28,
    23, 22, 17, 24, 25, 24,
    16, 18, 19, 23, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 15, 17, 15, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2376844875427930127806318510080, 5387515050969974956360988622848, 2376844875427930127806318510080, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 3, 4, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    20999999310609667, 24478637870169818, 26236844288704939, 23478116246970516, 16908826508416244, 28047069069087870,
    23047081798182412, 22908371912240472, 17815189385555479, 24193620029805483, 25661949713508626, 24193625443589029,
    16814945396983359, 18199255370559777, 19973880907651264, 23974288102537513, 16177166452380480
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3906890600547867, 4087462841250340, 3906890600547867, 0
  ]

abbrev PositiveTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 64474689 / 20000000000
noncomputable def negativeCeiling : ℝ := 3053909 / 6250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 158456249470664949272764481536, coefficient := 158456249470664949272764481536 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 441594780005295706300137603072, coefficient := 441594780005295706300137603072 }, { argument := 1493814950293925640692847083520, coefficient := 1493814950293925640692847083520 }, { argument := 441435145128708780813333823488, coefficient := 441435145128708780813333823488 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 74376138737241023400860712960, coefficient := 74376138737241023400860712960 }, { argument := 2619381547308206872347570864128, coefficient := 2619381547308206872347570864128 }, { argument := 2619404658569774036391246692352, coefficient := 2619404658569774036391246692352 }, { argument := 74352706354753024221310353408, coefficient := 74352706354753024221310353408 }, { argument := 5387515050969974956360988622848, coefficient := (-5387515050969974956360988622848) }, { argument := 4356383080447247709634560000, coefficient := 4356383080447247709634560000 }, { argument := 181215364169201403505007394816, coefficient := 181215364169201403505007394816 }, { argument := 2005701437597030619812777164800, coefficient := 2005701437597030619812777164800 }, { argument := 181216044189974936733918167040, coefficient := 181216044189974936733918167040 }, { argument := 4355646391275920044981223424, coefficient := 4355646391275920044981223424 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 2842571835965588500641742848, coefficient := 2842571835965588500641742848 }, { argument := 155613384847977422854119489536, coefficient := 155613384847977422854119489536 }, { argument := 155657312301001076293897289728, coefficient := 155657312301001076293897289728 }, { argument := 2799381072113262725517279232, coefficient := 2799381072113262725517279232 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5
