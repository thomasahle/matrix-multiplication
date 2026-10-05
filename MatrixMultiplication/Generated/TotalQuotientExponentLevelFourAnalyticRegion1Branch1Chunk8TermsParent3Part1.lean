import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-64538752254248527381896676507648)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    78351, 3813, 11685, 3813, 1019516153085, 151142912365315,
    16017, 41307, 34563, 966921, 37784848157879, 34563,
    31191, 16017, 16017, 31191, 966921, 31191,
    254875022153, 41307, 3441, 10545, 31191, 69597,
    3441, 34743, 70707, 3441, 10545, 3441,
    278292001, 18659621343, 35739, 92169, 77121, 2157507,
    18655769055, 77121, 69597, 35739, 35739, 69597,
    2157507, 69597, 278292001, 92169, 1584015, 1232826705,
    50300115603, 4931317321, 1584015, 1767, 5415, 16017,
    35739, 1767, 17841, 36309, 1767, 5415,
    1767, 1767, 5415, 16017
  ]
def negativeCoefficients : Array ℕ := #[
    5920034180789113154212724736, 288102134386911315197165568, 7063149101098470953220833280, 288102134386911315197165568, 2295746283565903777974190080, 340343581904062083098602373120,
    302552575824492429551075328, 390133584615792869684281344, 5223012887917553520671195136, 9132310643965600439344300032, 340335656168149273228469075968, 5223012887917553520671195136,
    294590665934374207720783872, 302552575824492429551075328, 302552575824492429551075328, 294590665934374207720783872, 9132310643965600439344300032, 294590665934374207720783872,
    2295710109588595426277195776, 390133584615792869684281344, 16249663067554449180327936, 398378836494883270227394560, 294590665934374207720783872, 328662540108278697937600512,
    16249663067554449180327936, 328138357428680167318880256, 333904366904264004124803072, 16249663067554449180327936, 398378836494883270227394560, 16249663067554449180327936,
    641697665025940326503677952, 43026157428331189314609217536, 337545311462556500584562688, 435255796359612329701146624, 5827098008406238536407187456, 10188538743356639636065615872,
    43017274656976911511962255360, 5827098008406238536407187456, 328662540108278697937600512, 337545311462556500584562688, 337545311462556500584562688, 328662540108278697937600512,
    10188538743356639636065615872, 328662540108278697937600512, 641697665025940326503677952, 435255796359612329701146624, 116879677255668141612072960, 22741638714369623645780705280,
    231968339851636399832523866112, 22741687141684503151781085184, 116879677255668141612072960, 16688843150461326185201664, 409145832075826061314621440, 302552575824492429551075328,
    337545311462556500584562688, 16688843150461326185201664, 337006961683509361030201344, 342928809253027896128176128, 16688843150461326185201664, 409145832075826061314621440,
    16688843150461326185201664, 16688843150461326185201664, 409145832075826061314621440, 302552575824492429551075328
  ]
def negativeScales : Array ℕ := #[
    16, 11, 13, 11, 39, 47,
    13, 15, 15, 19, 45, 15,
    14, 13, 13, 14, 19, 14,
    37, 15, 11, 13, 14, 16,
    11, 15, 16, 11, 13, 11,
    28, 34, 15, 16, 16, 21,
    34, 16, 16, 15, 15, 16,
    21, 16, 28, 16, 20, 30,
    35, 32, 20, 10, 12, 13,
    15, 10, 14, 15, 10, 12,
    10, 10, 12, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16257664067595541, 11896710819843133, 13512370113670596, 11896710819843133, 39891021775776666, 47102906655816359,
    13967316348309272, 15334098665057291, 15076940825560167, 19883038500170033, 45102873058729045, 15076940825560167,
    14928842193830838, 13967316348309272, 13967316348309272, 14928842193830838, 19883038500170033, 14928842193830838,
    37890999043111160, 15334098665057291, 11748612176955137, 13364271474681056, 14928842193830838, 16086737499152145,
    11748612176955137, 15084434713282725, 16109565428606407, 11748612176955137, 13364271474681056, 11748612176955137,
    28052024200705968, 34119200658958316, 15125211646966781, 16491993977638611, 16234836138141279, 21040933809539021,
    34118902783108478, 16234836138141279, 16086737499152145, 15125211646966781, 15125211646966781, 16086737499152145,
    21040933809539021, 16086737499152145, 28052024200705968, 16491993977638611, 20595154566566810, 30199322872374200,
    35549842664605216, 32199325944526278, 20595154566566810, 10787086325046961, 12402745622495697, 13967316348309272,
    15125211646966781, 10787086325046961, 14122908861097361, 15148039576421043, 10787086325046961, 12402745622495697,
    10787086325046961, 10787086325046961, 12402745622495697, 13967316348309272
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
noncomputable def negativeCeiling : ℝ := 550014973 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5920034180789113154212724736, coefficient := (-5920034180789113154212724736) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 7063149101098470953220833280, coefficient := (-7063149101098470953220833280) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 2295746283565903777974190080, coefficient := (-2295746283565903777974190080) }, { argument := 340343581904062083098602373120, coefficient := (-340343581904062083098602373120) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 390133584615792869684281344, coefficient := (-390133584615792869684281344) }, { argument := 5223012887917553520671195136, coefficient := (-5223012887917553520671195136) }, { argument := 9132310643965600439344300032, coefficient := (-9132310643965600439344300032) }, { argument := 340335656168149273228469075968, coefficient := (-340335656168149273228469075968) }, { argument := 5223012887917553520671195136, coefficient := (-5223012887917553520671195136) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 9132310643965600439344300032, coefficient := (-9132310643965600439344300032) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 2295710109588595426277195776, coefficient := (-2295710109588595426277195776) }, { argument := 390133584615792869684281344, coefficient := (-390133584615792869684281344) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 641697665025940326503677952, coefficient := (-641697665025940326503677952) }, { argument := 43026157428331189314609217536, coefficient := (-43026157428331189314609217536) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 435255796359612329701146624, coefficient := (-435255796359612329701146624) }, { argument := 5827098008406238536407187456, coefficient := (-5827098008406238536407187456) }, { argument := 10188538743356639636065615872, coefficient := (-10188538743356639636065615872) }, { argument := 43017274656976911511962255360, coefficient := (-43017274656976911511962255360) }, { argument := 5827098008406238536407187456, coefficient := (-5827098008406238536407187456) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 10188538743356639636065615872, coefficient := (-10188538743356639636065615872) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 641697665025940326503677952, coefficient := (-641697665025940326503677952) }, { argument := 435255796359612329701146624, coefficient := (-435255796359612329701146624) }, { argument := 116879677255668141612072960, coefficient := (-116879677255668141612072960) }, { argument := 22741638714369623645780705280, coefficient := (-22741638714369623645780705280) }, { argument := 231968339851636399832523866112, coefficient := (-231968339851636399832523866112) }, { argument := 22741687141684503151781085184, coefficient := (-22741687141684503151781085184) }, { argument := 116879677255668141612072960, coefficient := (-116879677255668141612072960) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }] }

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
def constantNumerator : ℤ := (-13530824458660764174842205306880)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    35739, 1767, 17841, 36309, 1767, 5415,
    1767, 27416555, 1824909333, 1767, 4557, 3813,
    106671, 1824528405, 3813, 3441, 1767, 1767,
    3441, 106671, 3441, 27416555, 4557, 3441,
    10545, 31191, 69597, 3441, 34743, 70707,
    3441, 10545, 3441, 106671, 326895, 966921,
    2157507, 106671, 1077033, 2191917, 106671, 326895,
    106671, 277997089, 18659400159, 17841, 46011, 38499,
    1077033, 18655554015, 38499, 34743, 17841, 17841,
    34743, 1077033, 34743, 277997089, 46011, 3441,
    10545, 31191, 69597, 3441
  ]
def negativeCoefficients : Array ℕ := #[
    337545311462556500584562688, 16688843150461326185201664, 337006961683509361030201344, 342928809253027896128176128, 16688843150461326185201664, 409145832075826061314621440,
    16688843150461326185201664, 31609135841736373494087680, 2103977213973437542205227008, 16688843150461326185201664, 21519824062436973238812672, 288102134386911315197165568,
    503739555094187924590166016, 2103538033890530665200353280, 288102134386911315197165568, 16249663067554449180327936, 16688843150461326185201664, 16688843150461326185201664,
    16249663067554449180327936, 503739555094187924590166016, 16249663067554449180327936, 31609135841736373494087680, 21519824062436973238812672, 16249663067554449180327936,
    398378836494883270227394560, 294590665934374207720783872, 328662540108278697937600512, 16249663067554449180327936, 328138357428680167318880256, 333904366904264004124803072,
    16249663067554449180327936, 398378836494883270227394560, 16249663067554449180327936, 503739555094187924590166016, 12349743931341381377049231360, 9132310643965600439344300032,
    10188538743356639636065615872, 503739555094187924590166016, 10172289080289085186885287936, 10351035374032184127868895232, 503739555094187924590166016, 12349743931341381377049231360,
    503739555094187924590166016, 641017644252407097592905728, 43025647412751039392926138368, 337006961683509361030201344, 434561608486630491854733312, 5817804391167951074626633728,
    10172289080289085186885287936, 43016778808496210199214817280, 5817804391167951074626633728, 328138357428680167318880256, 337006961683509361030201344, 337006961683509361030201344,
    328138357428680167318880256, 10172289080289085186885287936, 328138357428680167318880256, 641017644252407097592905728, 434561608486630491854733312, 16249663067554449180327936,
    398378836494883270227394560, 294590665934374207720783872, 328662540108278697937600512, 16249663067554449180327936
  ]
def negativeScales : Array ℕ := #[
    15, 10, 14, 15, 10, 12,
    10, 24, 30, 10, 12, 11,
    16, 30, 11, 11, 10, 10,
    11, 16, 11, 24, 12, 11,
    13, 14, 16, 11, 15, 16,
    11, 13, 11, 16, 18, 19,
    21, 16, 20, 21, 16, 18,
    16, 28, 34, 14, 15, 15,
    20, 34, 15, 15, 14, 14,
    15, 20, 15, 28, 15, 11,
    13, 14, 16, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15125211646966781, 10787086325046961, 14122908861097361, 15148039576421043, 10787086325046961, 12402745622495697,
    10787086325046961, 24708543966392326, 30765177642630532, 10787086325046961, 12153868655223240, 11896710819843133,
    16702808487201178, 30764876465856659, 11896710819843133, 11748612176955137, 10787086325046961, 10787086325046961,
    11748612176955137, 16702808487201178, 11748612176955137, 24708543966392326, 12153868655223240, 11748612176955137,
    13364271474681056, 14928842193830838, 16086737499152145, 11748612176955137, 15084434713282725, 16109565428606407,
    11748612176955137, 13364271474681056, 11748612176955137, 16702808487201178, 18318467785067930, 19883038500170033,
    21040933809539021, 16702808487201178, 20038631023669600, 21063761738993282, 16702808487201178, 18318467785067930,
    16702808487201178, 28050494535187063, 34119183557702866, 14122908861097361, 15489691191769175, 15232533352271859,
    20038631023669600, 34118886153457420, 15232533352271859, 15084434713282725, 14122908861097361, 14122908861097361,
    15084434713282725, 20038631023669600, 15084434713282725, 28050494535187063, 15489691191769175, 11748612176955137,
    13364271474681056, 14928842193830838, 16086737499152145, 11748612176955137
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
noncomputable def negativeCeiling : ℝ := 12342579 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 31609135841736373494087680, coefficient := (-31609135841736373494087680) }, { argument := 2103977213973437542205227008, coefficient := (-2103977213973437542205227008) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 2103538033890530665200353280, coefficient := (-2103538033890530665200353280) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 31609135841736373494087680, coefficient := (-31609135841736373494087680) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 333904366904264004124803072, coefficient := (-333904366904264004124803072) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 12349743931341381377049231360, coefficient := (-12349743931341381377049231360) }, { argument := 9132310643965600439344300032, coefficient := (-9132310643965600439344300032) }, { argument := 10188538743356639636065615872, coefficient := (-10188538743356639636065615872) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 10172289080289085186885287936, coefficient := (-10172289080289085186885287936) }, { argument := 10351035374032184127868895232, coefficient := (-10351035374032184127868895232) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 12349743931341381377049231360, coefficient := (-12349743931341381377049231360) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 641017644252407097592905728, coefficient := (-641017644252407097592905728) }, { argument := 43025647412751039392926138368, coefficient := (-43025647412751039392926138368) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 434561608486630491854733312, coefficient := (-434561608486630491854733312) }, { argument := 5817804391167951074626633728, coefficient := (-5817804391167951074626633728) }, { argument := 10172289080289085186885287936, coefficient := (-10172289080289085186885287936) }, { argument := 43016778808496210199214817280, coefficient := (-43016778808496210199214817280) }, { argument := 5817804391167951074626633728, coefficient := (-5817804391167951074626633728) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 10172289080289085186885287936, coefficient := (-10172289080289085186885287936) }, { argument := 328138357428680167318880256, coefficient := (-328138357428680167318880256) }, { argument := 641017644252407097592905728, coefficient := (-641017644252407097592905728) }, { argument := 434561608486630491854733312, coefficient := (-434561608486630491854733312) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 294590665934374207720783872, coefficient := (-294590665934374207720783872) }, { argument := 328662540108278697937600512, coefficient := (-328662540108278697937600512) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
