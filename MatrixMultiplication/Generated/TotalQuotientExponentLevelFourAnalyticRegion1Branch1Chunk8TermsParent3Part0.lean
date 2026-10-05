import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-147521621479942117898209680424960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    940545, 1584015, 6324495, 3148755, 6324495, 36808191,
    1232826705, 4925839185, 2456540685, 4925839185, 30940127771, 669496571,
    1019516153085, 278292001, 27416555, 277997089, 562187661, 3878792925,
    669496571, 27416555, 36808191, 50300115603, 200992915347, 100254319431,
    200992915347, 3898954948069, 44213881605, 151142912365315, 18659621343, 1824909333,
    18659400159, 37265240691, 489347240227, 44213881605, 1824909333, 1767,
    5415, 16017, 35739, 1767, 17841, 36309,
    1767, 5415, 1767, 30940127771, 3898954948069, 1767,
    4557, 3813, 106671, 974690067089, 3813, 3441,
    1767, 1767, 3441, 106671, 3441, 7734943087,
    4557, 4557, 13965, 41307
  ]
def negativeCoefficients : Array ℕ := #[
    8883196367261260915031408640, 116879677255668141612072960, 116666340660455690647633920, 116168555271626638397276160, 116666340660455690647633920, 347643534946928258255916367872,
    22741638714369623645780705280, 22716423698486259414718218240, 22657588661425076208905748480, 22716423698486259414718218240, 69670973950135567497822208, 771876993966444753553719296,
    2295746283565903777974190080, 641697665025940326503677952, 31609135841736373494087680, 641017644252407097592905728, 648158243991524026022363136, 69874121486709264954163200,
    771876993966444753553719296, 31609135841736373494087680, 347643534946928258255916367872, 231968339851636399832523866112, 231729054377179864763750940672, 231170721603447949603280781312,
    231729054377179864763750940672, 8779666025628949991351386112, 50975134904545594269216276480, 340343581904062083098602373120, 43026157428331189314609217536, 2103977213973437542205227008,
    43025647412751039392926138368, 42963897367004017887245500416, 8815296194964391161776570368, 50975134904545594269216276480, 2103977213973437542205227008, 16688843150461326185201664,
    409145832075826061314621440, 302552575824492429551075328, 337545311462556500584562688, 16688843150461326185201664, 337006961683509361030201344, 342928809253027896128176128,
    16688843150461326185201664, 409145832075826061314621440, 16688843150461326185201664, 69670973950135567497822208, 8779666025628949991351386112, 16688843150461326185201664,
    21519824062436973238812672, 288102134386911315197165568, 503739555094187924590166016, 8779227645887488293798412288, 288102134386911315197165568, 16249663067554449180327936,
    16688843150461326185201664, 16688843150461326185201664, 16249663067554449180327936, 503739555094187924590166016, 16249663067554449180327936, 69670173608690388045922304,
    21519824062436973238812672, 21519824062436973238812672, 527582783466196763274117120, 390133584615792869684281344
  ]
def negativeScales : Array ℕ := #[
    19, 20, 22, 21, 22, 25,
    30, 32, 31, 32, 34, 29,
    39, 28, 24, 28, 29, 31,
    29, 24, 25, 35, 37, 36,
    37, 41, 35, 47, 34, 30,
    34, 35, 38, 35, 30, 10,
    12, 13, 15, 10, 14, 15,
    10, 12, 10, 34, 41, 10,
    12, 11, 16, 39, 11, 11,
    10, 10, 11, 16, 11, 32,
    12, 12, 13, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19843137446523372, 20595154566566810, 22592518857027880, 21586350077186946, 22592518857027880, 25133523512019350,
    30199322872374200, 32197722382596552, 31193980987055114, 32197722382596552, 34848760105148126, 29318501425531288,
    39891021775776666, 28052024200705968, 24708543966392326, 28050494535187063, 29066476548623874, 31852960613371654,
    29318501425531288, 24708543966392326, 25133523512019350, 35549842664605216, 37548353693555094, 36544873439918004,
    37548353693555094, 41826224624414088, 35363780345152980, 47102906655816359, 34119200658958316, 30765177642630532,
    34119183557702866, 35117111526729437, 38832067608262818, 35363780345152980, 30765177642630532, 10787086325046961,
    12402745622495697, 13967316348309272, 15125211646966781, 10787086325046961, 14122908861097361, 15148039576421043,
    10787086325046961, 12402745622495697, 10787086325046961, 34848760105148126, 41826224624414088, 10787086325046961,
    12153868655223240, 11896710819843133, 16702808487201178, 39826152587040369, 11896710819843133, 11748612176955137,
    10787086325046961, 10787086325046961, 11748612176955137, 16702808487201178, 11748612176955137, 32848743532173214,
    12153868655223240, 12153868655223240, 13769527953509885, 15334098665057291
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
noncomputable def negativeCeiling : ℝ := 969263219 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8883196367261260915031408640, coefficient := (-8883196367261260915031408640) }, { argument := 116879677255668141612072960, coefficient := (-116879677255668141612072960) }, { argument := 116666340660455690647633920, coefficient := (-116666340660455690647633920) }, { argument := 116168555271626638397276160, coefficient := (-116168555271626638397276160) }, { argument := 116666340660455690647633920, coefficient := (-116666340660455690647633920) }, { argument := 347643534946928258255916367872, coefficient := (-347643534946928258255916367872) }, { argument := 22741638714369623645780705280, coefficient := (-22741638714369623645780705280) }, { argument := 22716423698486259414718218240, coefficient := (-22716423698486259414718218240) }, { argument := 22657588661425076208905748480, coefficient := (-22657588661425076208905748480) }, { argument := 22716423698486259414718218240, coefficient := (-22716423698486259414718218240) }, { argument := 69670973950135567497822208, coefficient := (-69670973950135567497822208) }, { argument := 771876993966444753553719296, coefficient := (-771876993966444753553719296) }, { argument := 2295746283565903777974190080, coefficient := (-2295746283565903777974190080) }, { argument := 641697665025940326503677952, coefficient := (-641697665025940326503677952) }, { argument := 31609135841736373494087680, coefficient := (-31609135841736373494087680) }, { argument := 641017644252407097592905728, coefficient := (-641017644252407097592905728) }, { argument := 648158243991524026022363136, coefficient := (-648158243991524026022363136) }, { argument := 69874121486709264954163200, coefficient := (-69874121486709264954163200) }, { argument := 771876993966444753553719296, coefficient := (-771876993966444753553719296) }, { argument := 31609135841736373494087680, coefficient := (-31609135841736373494087680) }, { argument := 347643534946928258255916367872, coefficient := (-347643534946928258255916367872) }, { argument := 231968339851636399832523866112, coefficient := (-231968339851636399832523866112) }, { argument := 231729054377179864763750940672, coefficient := (-231729054377179864763750940672) }, { argument := 231170721603447949603280781312, coefficient := (-231170721603447949603280781312) }, { argument := 231729054377179864763750940672, coefficient := (-231729054377179864763750940672) }, { argument := 8779666025628949991351386112, coefficient := (-8779666025628949991351386112) }, { argument := 50975134904545594269216276480, coefficient := (-50975134904545594269216276480) }, { argument := 340343581904062083098602373120, coefficient := (-340343581904062083098602373120) }, { argument := 43026157428331189314609217536, coefficient := (-43026157428331189314609217536) }, { argument := 2103977213973437542205227008, coefficient := (-2103977213973437542205227008) }, { argument := 43025647412751039392926138368, coefficient := (-43025647412751039392926138368) }, { argument := 42963897367004017887245500416, coefficient := (-42963897367004017887245500416) }, { argument := 8815296194964391161776570368, coefficient := (-8815296194964391161776570368) }, { argument := 50975134904545594269216276480, coefficient := (-50975134904545594269216276480) }, { argument := 2103977213973437542205227008, coefficient := (-2103977213973437542205227008) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 342928809253027896128176128, coefficient := (-342928809253027896128176128) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 69670973950135567497822208, coefficient := (-69670973950135567497822208) }, { argument := 8779666025628949991351386112, coefficient := (-8779666025628949991351386112) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 8779227645887488293798412288, coefficient := (-8779227645887488293798412288) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 69670173608690388045922304, coefficient := (-69670173608690388045922304) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 527582783466196763274117120, coefficient := (-527582783466196763274117120) }, { argument := 390133584615792869684281344, coefficient := (-390133584615792869684281344) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-58662290743019364067672930123776)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    92169, 4557, 46011, 93639, 4557, 13965,
    4557, 3813, 11685, 34563, 77121, 3813,
    38499, 78351, 3813, 11685, 3813, 106671,
    326895, 966921, 2157507, 106671, 1077033, 2191917,
    106671, 326895, 106671, 669496571, 44213881605, 5415,
    13965, 11685, 326895, 44204542725, 11685, 10545,
    5415, 5415, 10545, 326895, 10545, 669496571,
    13965, 940545, 4931317321, 19703398729, 9826183717, 19703398729,
    974690067089, 44204542725, 37784848157879, 18655769055, 1824528405, 18655554015,
    37257413235, 122330726375, 44204542725, 1824528405, 3813, 11685,
    34563, 77121, 3813, 38499
  ]
def negativeCoefficients : Array ℕ := #[
    435255796359612329701146624, 21519824062436973238812672, 434561608486630491854733312, 442197675089430708165279744, 21519824062436973238812672, 527582783466196763274117120,
    21519824062436973238812672, 288102134386911315197165568, 7063149101098470953220833280, 5223012887917553520671195136, 5827098008406238536407187456, 288102134386911315197165568,
    5817804391167951074626633728, 5920034180789113154212724736, 288102134386911315197165568, 7063149101098470953220833280, 288102134386911315197165568, 503739555094187924590166016,
    12349743931341381377049231360, 9132310643965600439344300032, 10188538743356639636065615872, 503739555094187924590166016, 10172289080289085186885287936, 10351035374032184127868895232,
    503739555094187924590166016, 12349743931341381377049231360, 503739555094187924590166016, 771876993966444753553719296, 50975134904545594269216276480, 409145832075826061314621440,
    527582783466196763274117120, 7063149101098470953220833280, 12349743931341381377049231360, 50964367908964651478129049600, 7063149101098470953220833280, 398378836494883270227394560,
    409145832075826061314621440, 409145832075826061314621440, 398378836494883270227394560, 12349743931341381377049231360, 398378836494883270227394560, 771876993966444753553719296,
    527582783466196763274117120, 8883196367261260915031408640, 22741687141684503151781085184, 22716472108507316351615893504, 22657637031093880484563779584, 22716472108507316351615893504,
    8779227645887488293798412288, 50964367908964651478129049600, 340335656168149273228469075968, 43017274656976911511962255360, 2103538033890530665200353280, 43016778808496210199214817280,
    42954872924655253995242127360, 8814857819494593710784512000, 50964367908964651478129049600, 2103538033890530665200353280, 288102134386911315197165568, 7063149101098470953220833280,
    5223012887917553520671195136, 5827098008406238536407187456, 288102134386911315197165568, 5817804391167951074626633728
  ]
def negativeScales : Array ℕ := #[
    16, 12, 15, 16, 12, 13,
    12, 11, 13, 15, 16, 11,
    15, 16, 11, 13, 11, 16,
    18, 19, 21, 16, 20, 21,
    16, 18, 16, 29, 35, 12,
    13, 13, 18, 35, 13, 13,
    12, 12, 13, 18, 13, 29,
    13, 19, 32, 34, 33, 34,
    39, 35, 45, 34, 30, 34,
    35, 36, 35, 30, 11, 13,
    15, 16, 11, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16491993977638611, 12153868655223240, 15489691191769175, 16514821907093107, 12153868655223240, 13769527953509885,
    12153868655223240, 11896710819843133, 13512370113670596, 15076940825560167, 16234836138141279, 11896710819843133,
    15232533352271859, 16257664067595541, 11896710819843133, 13512370113670596, 11896710819843133, 16702808487201178,
    18318467785067930, 19883038500170033, 21040933809539021, 16702808487201178, 20038631023669600, 21063761738993282,
    16702808487201178, 18318467785067930, 16702808487201178, 29318501425531288, 35363780345152980, 12402745622495697,
    13769527953509885, 13512370113670596, 18318467785067930, 35363475586138880, 13512370113670596, 13364271474681056,
    12402745622495697, 12402745622495697, 13364271474681056, 18318467785067930, 13364271474681056, 29318501425531288,
    13769527953509885, 19843137446523372, 32199325944526278, 34197725457060377, 33193984066933025, 34197725457060377,
    39826152587040369, 35363475586138880, 45102873058729045, 34118902783108478, 30764876465856659, 34118886153457420,
    35116808460979612, 36831995862760077, 35363475586138880, 30764876465856659, 11896710819843133, 13512370113670596,
    15076940825560167, 16234836138141279, 11896710819843133, 15232533352271859
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
noncomputable def negativeCeiling : ℝ := 204727043 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 435255796359612329701146624, coefficient := (-435255796359612329701146624) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 434561608486630491854733312, coefficient := (-434561608486630491854733312) }, { argument := 442197675089430708165279744, coefficient := (-442197675089430708165279744) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 527582783466196763274117120, coefficient := (-527582783466196763274117120) }, { argument := 21519824062436973238812672, coefficient := (-21519824062436973238812672) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 7063149101098470953220833280, coefficient := (-7063149101098470953220833280) }, { argument := 5223012887917553520671195136, coefficient := (-5223012887917553520671195136) }, { argument := 5827098008406238536407187456, coefficient := (-5827098008406238536407187456) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 5817804391167951074626633728, coefficient := (-5817804391167951074626633728) }, { argument := 5920034180789113154212724736, coefficient := (-5920034180789113154212724736) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 7063149101098470953220833280, coefficient := (-7063149101098470953220833280) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 12349743931341381377049231360, coefficient := (-12349743931341381377049231360) }, { argument := 9132310643965600439344300032, coefficient := (-9132310643965600439344300032) }, { argument := 10188538743356639636065615872, coefficient := (-10188538743356639636065615872) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 10172289080289085186885287936, coefficient := (-10172289080289085186885287936) }, { argument := 10351035374032184127868895232, coefficient := (-10351035374032184127868895232) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 12349743931341381377049231360, coefficient := (-12349743931341381377049231360) }, { argument := 503739555094187924590166016, coefficient := (-503739555094187924590166016) }, { argument := 771876993966444753553719296, coefficient := (-771876993966444753553719296) }, { argument := 50975134904545594269216276480, coefficient := (-50975134904545594269216276480) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 527582783466196763274117120, coefficient := (-527582783466196763274117120) }, { argument := 7063149101098470953220833280, coefficient := (-7063149101098470953220833280) }, { argument := 12349743931341381377049231360, coefficient := (-12349743931341381377049231360) }, { argument := 50964367908964651478129049600, coefficient := (-50964367908964651478129049600) }, { argument := 7063149101098470953220833280, coefficient := (-7063149101098470953220833280) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 12349743931341381377049231360, coefficient := (-12349743931341381377049231360) }, { argument := 398378836494883270227394560, coefficient := (-398378836494883270227394560) }, { argument := 771876993966444753553719296, coefficient := (-771876993966444753553719296) }, { argument := 527582783466196763274117120, coefficient := (-527582783466196763274117120) }, { argument := 8883196367261260915031408640, coefficient := (-8883196367261260915031408640) }, { argument := 22741687141684503151781085184, coefficient := (-22741687141684503151781085184) }, { argument := 22716472108507316351615893504, coefficient := (-22716472108507316351615893504) }, { argument := 22657637031093880484563779584, coefficient := (-22657637031093880484563779584) }, { argument := 22716472108507316351615893504, coefficient := (-22716472108507316351615893504) }, { argument := 8779227645887488293798412288, coefficient := (-8779227645887488293798412288) }, { argument := 50964367908964651478129049600, coefficient := (-50964367908964651478129049600) }, { argument := 340335656168149273228469075968, coefficient := (-340335656168149273228469075968) }, { argument := 43017274656976911511962255360, coefficient := (-43017274656976911511962255360) }, { argument := 2103538033890530665200353280, coefficient := (-2103538033890530665200353280) }, { argument := 43016778808496210199214817280, coefficient := (-43016778808496210199214817280) }, { argument := 42954872924655253995242127360, coefficient := (-42954872924655253995242127360) }, { argument := 8814857819494593710784512000, coefficient := (-8814857819494593710784512000) }, { argument := 50964367908964651478129049600, coefficient := (-50964367908964651478129049600) }, { argument := 2103538033890530665200353280, coefficient := (-2103538033890530665200353280) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 7063149101098470953220833280, coefficient := (-7063149101098470953220833280) }, { argument := 5223012887917553520671195136, coefficient := (-5223012887917553520671195136) }, { argument := 5827098008406238536407187456, coefficient := (-5827098008406238536407187456) }, { argument := 288102134386911315197165568, coefficient := (-288102134386911315197165568) }, { argument := 5817804391167951074626633728, coefficient := (-5817804391167951074626633728) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
