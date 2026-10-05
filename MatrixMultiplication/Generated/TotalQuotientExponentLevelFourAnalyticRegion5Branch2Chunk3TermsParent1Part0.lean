import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 3, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3

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
def constantNumerator : ℤ := (-54191659827300187500480726827008)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    120607310505, 96481345611, 12349550700037, 241066028841, 35116769929, 430498039333,
    9417910090817, 430263294031, 17087132199, 35116769929, 1282242508449, 1282243933857,
    35115954229, 433015818675, 346396488585, 44338529598695, 865498147635, 1282242508449,
    15811197087655, 690488586993525, 63210293840305, 624794337983, 430498039333, 15811197087655,
    15811211745739, 430488629353, 120607310505, 433015818675, 30110866665, 30110866665,
    24087569163, 3083193489221, 60184635753, 1282243933857, 15811211745739, 690489269550741,
    63210352428913, 624795007331, 9417910090817, 690488586993525, 690489269550741, 4708848829021,
    96481345611, 346396488585, 24087569163, 35115954229, 430488629353, 4708848829021,
    860507801297, 17086730679, 430263294031, 63210293840305, 63210352428913, 860507801297,
    12349550700037, 44338529598695, 3083193489221, 17087132199, 624794337983, 624795007331,
    17086730679, 241066028841, 865498147635, 60184635753
  ]
def negativeCoefficients : Array ℕ := #[
    135791759662118926936965120, 6952213634270458235527888896, 6952178991359960152794988544, 135708109707501605216059392, 19768983995837479909326848, 484697702380956982592929792,
    5301812046951534417783291904, 484433402667303438955577344, 19238400551061700976050176, 19768983995837479909326848, 721838360406190808616665088, 721839162839558014982160384,
    19768524797560474145128448, 487532469907565065745203200, 24960497550621668339676610560, 24960373172354813693620387840, 487232141897355066731397120, 721838360406190808616665088,
    17801825328061132395218206720, 194355258942976218808870502400, 17792115986573572287055790080, 703455886930858633846587392, 484697702380956982592929792, 17801825328061132395218206720,
    17801841831596542486575579136, 484687107685351591637942272, 135791759662118926936965120, 487532469907565065745203200, 135607287892296689610915840, 135607287892296689610915840,
    6942769120431862414439350272, 6942734524583417487774711808, 135523751575319915469471744, 721839162839558014982160384, 17801841831596542486575579136, 194355451065752696099067396096,
    17792132477800644596809596928, 703456640549709479143276544, 5301812046951534417783291904, 194355258942976218808870502400, 194355451065752696099067396096, 5301692457930743007730991104,
    6952213634270458235527888896, 24960497550621668339676610560, 6942769120431862414439350272, 19768524797560474145128448, 484687107685351591637942272, 5301692457930743007730991104,
    484422826658821751821041664, 19237948479731105525661696, 484433402667303438955577344, 17792115986573572287055790080, 17792132477800644596809596928, 484422826658821751821041664,
    6952178991359960152794988544, 24960373172354813693620387840, 6942734524583417487774711808, 19238400551061700976050176, 703455886930858633846587392, 703456640549709479143276544,
    19237948479731105525661696, 135708109707501605216059392, 487232141897355066731397120, 135523751575319915469471744
  ]
def negativeScales : Array ℕ := #[
    36, 36, 43, 37, 35, 38,
    43, 38, 33, 35, 40, 40,
    35, 38, 38, 45, 39, 40,
    43, 49, 45, 39, 38, 43,
    43, 38, 36, 38, 34, 34,
    34, 41, 35, 40, 43, 49,
    45, 39, 43, 49, 49, 42,
    36, 38, 34, 35, 38, 42,
    39, 33, 38, 45, 45, 39,
    43, 45, 41, 33, 39, 39,
    33, 37, 39, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36811526402143528, 36489530977305625, 43489523788332108, 37810637404437890, 35031441099506502, 38647215710785067,
    43098544088494157, 38646428812306925, 33992191253881186, 35031441099506502, 40221806280987132, 40221807884761688,
    35031407587881856, 38655628773372938, 38333633349325961, 45333626160352444, 39654739775681190, 40221806280987132,
    43846011835413924, 49294610896962996, 45845224756541916, 39184590423295841, 38647215710785067, 43846011835413924,
    43846013172892410, 38647184175496585, 36811526402143528, 38655628773372938, 34809565182639123, 34809565182639123,
    34487569757832737, 41487562568859220, 35808676184934007, 40221807884761688, 43846013172892410, 49294612323085661,
    45845226093752242, 39184591968867662, 43098544088494157, 49294610896962996, 49294612323085661, 42098511546330919,
    36489530977305625, 38333633349325961, 34487569757832737, 35031407587881856, 38647184175496585, 42098511546330919,
    39646397315466558, 33992157352468896, 38646428812306925, 45845224756541916, 45845226093752242, 39646397315466558,
    43489523788332108, 45333626160352444, 41487562568859220, 33992191253881186, 39184590423295841, 39184591968867662,
    33992157352468896, 37810637404437890, 39654739775681190, 35808676184934007
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
noncomputable def negativeCeiling : ℝ := 631380313 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 135791759662118926936965120, coefficient := (-135791759662118926936965120) }, { argument := 6952213634270458235527888896, coefficient := (-6952213634270458235527888896) }, { argument := 6952178991359960152794988544, coefficient := (-6952178991359960152794988544) }, { argument := 135708109707501605216059392, coefficient := (-135708109707501605216059392) }, { argument := 19768983995837479909326848, coefficient := (-19768983995837479909326848) }, { argument := 484697702380956982592929792, coefficient := (-484697702380956982592929792) }, { argument := 5301812046951534417783291904, coefficient := (-5301812046951534417783291904) }, { argument := 484433402667303438955577344, coefficient := (-484433402667303438955577344) }, { argument := 19238400551061700976050176, coefficient := (-19238400551061700976050176) }, { argument := 19768983995837479909326848, coefficient := (-19768983995837479909326848) }, { argument := 721838360406190808616665088, coefficient := (-721838360406190808616665088) }, { argument := 721839162839558014982160384, coefficient := (-721839162839558014982160384) }, { argument := 19768524797560474145128448, coefficient := (-19768524797560474145128448) }, { argument := 487532469907565065745203200, coefficient := (-487532469907565065745203200) }, { argument := 24960497550621668339676610560, coefficient := (-24960497550621668339676610560) }, { argument := 24960373172354813693620387840, coefficient := (-24960373172354813693620387840) }, { argument := 487232141897355066731397120, coefficient := (-487232141897355066731397120) }, { argument := 721838360406190808616665088, coefficient := (-721838360406190808616665088) }, { argument := 17801825328061132395218206720, coefficient := (-17801825328061132395218206720) }, { argument := 194355258942976218808870502400, coefficient := (-194355258942976218808870502400) }, { argument := 17792115986573572287055790080, coefficient := (-17792115986573572287055790080) }, { argument := 703455886930858633846587392, coefficient := (-703455886930858633846587392) }, { argument := 484697702380956982592929792, coefficient := (-484697702380956982592929792) }, { argument := 17801825328061132395218206720, coefficient := (-17801825328061132395218206720) }, { argument := 17801841831596542486575579136, coefficient := (-17801841831596542486575579136) }, { argument := 484687107685351591637942272, coefficient := (-484687107685351591637942272) }, { argument := 135791759662118926936965120, coefficient := (-135791759662118926936965120) }, { argument := 487532469907565065745203200, coefficient := (-487532469907565065745203200) }, { argument := 135607287892296689610915840, coefficient := (-135607287892296689610915840) }, { argument := 135607287892296689610915840, coefficient := (-135607287892296689610915840) }, { argument := 6942769120431862414439350272, coefficient := (-6942769120431862414439350272) }, { argument := 6942734524583417487774711808, coefficient := (-6942734524583417487774711808) }, { argument := 135523751575319915469471744, coefficient := (-135523751575319915469471744) }, { argument := 721839162839558014982160384, coefficient := (-721839162839558014982160384) }, { argument := 17801841831596542486575579136, coefficient := (-17801841831596542486575579136) }, { argument := 194355451065752696099067396096, coefficient := (-194355451065752696099067396096) }, { argument := 17792132477800644596809596928, coefficient := (-17792132477800644596809596928) }, { argument := 703456640549709479143276544, coefficient := (-703456640549709479143276544) }, { argument := 5301812046951534417783291904, coefficient := (-5301812046951534417783291904) }, { argument := 194355258942976218808870502400, coefficient := (-194355258942976218808870502400) }, { argument := 194355451065752696099067396096, coefficient := (-194355451065752696099067396096) }, { argument := 5301692457930743007730991104, coefficient := (-5301692457930743007730991104) }, { argument := 6952213634270458235527888896, coefficient := (-6952213634270458235527888896) }, { argument := 24960497550621668339676610560, coefficient := (-24960497550621668339676610560) }, { argument := 6942769120431862414439350272, coefficient := (-6942769120431862414439350272) }, { argument := 19768524797560474145128448, coefficient := (-19768524797560474145128448) }, { argument := 484687107685351591637942272, coefficient := (-484687107685351591637942272) }, { argument := 5301692457930743007730991104, coefficient := (-5301692457930743007730991104) }, { argument := 484422826658821751821041664, coefficient := (-484422826658821751821041664) }, { argument := 19237948479731105525661696, coefficient := (-19237948479731105525661696) }, { argument := 484433402667303438955577344, coefficient := (-484433402667303438955577344) }, { argument := 17792115986573572287055790080, coefficient := (-17792115986573572287055790080) }, { argument := 17792132477800644596809596928, coefficient := (-17792132477800644596809596928) }, { argument := 484422826658821751821041664, coefficient := (-484422826658821751821041664) }, { argument := 6952178991359960152794988544, coefficient := (-6952178991359960152794988544) }, { argument := 24960373172354813693620387840, coefficient := (-24960373172354813693620387840) }, { argument := 6942734524583417487774711808, coefficient := (-6942734524583417487774711808) }, { argument := 19238400551061700976050176, coefficient := (-19238400551061700976050176) }, { argument := 703455886930858633846587392, coefficient := (-703455886930858633846587392) }, { argument := 703456640549709479143276544, coefficient := (-703456640549709479143276544) }, { argument := 19237948479731105525661696, coefficient := (-19237948479731105525661696) }, { argument := 135708109707501605216059392, coefficient := (-135708109707501605216059392) }, { argument := 487232141897355066731397120, coefficient := (-487232141897355066731397120) }, { argument := 135523751575319915469471744, coefficient := (-135523751575319915469471744) }] }

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
def constantNumerator : ℤ := 54058728785496518520011889836032
def positiveArguments : Array ℕ := #[
    7, 1500931, 5388785, 374723, 167023, 48995455,
    48995503, 668077, 314083, 7744645, 42279037, 7740421,
    306073, 80355, 64281, 8227927, 160611
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 28351784990000077840951803904, 101791270669562804331547197440, 28313269368965793014588899328, 12619901073093388040434352128, 462748989009895945867215503360,
    462749442357078301353156018176, 12619617731104415861721530368, 2966430064078293555306561536, 73146103939447966912049315840, 798628429027222384666904363008, 73106209387400684149284012032,
    2890777753022721838983151616, 1517863034923961364586168320, 77710960610647977979287699456, 77710573376596382668380176384, 1516928006360353174833856512
  ]
def positiveScales : Array ℕ := #[
    2, 20, 22, 18, 17, 25,
    25, 19, 18, 22, 25, 22,
    18, 16, 15, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 20517426224999651, 22361528597020208, 18515465005526778, 17349687257981427, 25546144589907073,
    25546146003289764, 19349654866232158, 18260786332487424, 22884767679215037, 25333439180687414, 22883980605529820,
    18223516258654385, 16294100176328157, 15972104751376100, 22972097562402693, 17293211178636955
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 21578389 / 31250000000
noncomputable def negativeCeiling : ℝ := 36276913 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 28351784990000077840951803904, coefficient := 28351784990000077840951803904 }, { argument := 101791270669562804331547197440, coefficient := 101791270669562804331547197440 }, { argument := 28313269368965793014588899328, coefficient := 28313269368965793014588899328 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 12619901073093388040434352128, coefficient := 12619901073093388040434352128 }, { argument := 462748989009895945867215503360, coefficient := 462748989009895945867215503360 }, { argument := 462749442357078301353156018176, coefficient := 462749442357078301353156018176 }, { argument := 12619617731104415861721530368, coefficient := 12619617731104415861721530368 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 2966430064078293555306561536, coefficient := 2966430064078293555306561536 }, { argument := 73146103939447966912049315840, coefficient := 73146103939447966912049315840 }, { argument := 798628429027222384666904363008, coefficient := 798628429027222384666904363008 }, { argument := 73106209387400684149284012032, coefficient := 73106209387400684149284012032 }, { argument := 2890777753022721838983151616, coefficient := 2890777753022721838983151616 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 1517863034923961364586168320, coefficient := 1517863034923961364586168320 }, { argument := 77710960610647977979287699456, coefficient := 77710960610647977979287699456 }, { argument := 77710573376596382668380176384, coefficient := 77710573376596382668380176384 }, { argument := 1516928006360353174833856512, coefficient := 1516928006360353174833856512 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3
