import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-171465231383181429270694697369600)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    809107739, 4668653285, 37, 3, 643, 1163,
    4668653285, 643, 19, 19, 37, 37,
    1163, 37, 809107739, 3, 17605857, 4192660587,
    3605782257, 1455122325, 140485023, 234141705, 7164736173, 234141705,
    140485023, 114776263791, 7352049537, 4192660587, 7164736173, 234141705,
    7352049537, 234141705, 7164736173, 234141705, 17605857, 22514405,
    4465390875, 4465390875, 22514405, 60426111, 2475668955, 50975940885,
    2475668955, 60426111, 755141989, 107468025, 3834207383, 1212853425,
    107468025, 7668412937, 107468025, 107468025, 4455317265, 27634635,
    1212853425, 4455317265, 755141989, 107468025, 27634635, 107468025,
    1567943, 64238915, 1322729005, 64238915
  ]
def negativeCoefficients : Array ℕ := #[
    1865675423673848081340694528, 10765181539659797535989432320, 1431368170423720942852112384, 1856910058928070412348686336, 24874857664390609898754277376, 44991383302778039365865046016,
    10765181539659797535989432320, 24874857664390609898754277376, 1470053796651389076442710016, 1470053796651389076442710016, 1431368170423720942852112384, 1431368170423720942852112384,
    44991383302778039365865046016, 1431368170423720942852112384, 1865675423673848081340694528, 1856910058928070412348686336, 2598165906218622602283319296, 38670468418158929972922679296,
    66514942480401801388398477312, 13421134562608107061090713600, 41463860247523200865495154688, 2159576054558500045077872640, 66083027269490101379382902784, 69106433745872001442491924480,
    41463860247523200865495154688, 1058624181944576722097173168128, 67810688113136901415445200896, 38670468418158929972922679296, 66083027269490101379382902784, 2159576054558500045077872640,
    67810688113136901415445200896, 2159576054558500045077872640, 66083027269490101379382902784, 69106433745872001442491924480, 2598165906218622602283319296, 51914683375855837181378560,
    10296490332525369898303488000, 10296490332525369898303488000, 51914683375855837181378560, 139333125623320693463580672, 22834015812056484311350640640, 235085033855535546459268055040,
    22834015812056484311350640640, 139333125623320693463580672, 3482477752598748353901101056, 1982435153282019935807078400, 70728642319728659003686780928, 22373196729897082132679884800,
    1982435153282019935807078400, 70728625450181203596301828096, 1982435153282019935807078400, 1982435153282019935807078400, 82186097354634597910173450240, 2039076157661506219687280640,
    22373196729897082132679884800, 82186097354634597910173450240, 3482477752598748353901101056, 1982435153282019935807078400, 2039076157661506219687280640, 1982435153282019935807078400,
    7230860810791093872361472, 1184998824577781620948336640, 12200021717053740934013911040, 1184998824577781620948336640
  ]
def negativeScales : Array ℕ := #[
    29, 32, 5, 1, 9, 10,
    32, 9, 4, 4, 5, 5,
    10, 5, 29, 1, 24, 31,
    31, 30, 27, 27, 32, 27,
    27, 36, 32, 31, 32, 27,
    32, 27, 32, 27, 24, 24,
    32, 32, 24, 25, 31, 35,
    31, 25, 29, 26, 31, 30,
    26, 32, 26, 26, 32, 24,
    30, 32, 29, 26, 24, 26,
    20, 25, 30, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29591756580636139, 32120359305581071, 5209453365628950, 1584962500724866, 9328674927327948, 10183635381473219,
    32120359305581071, 9328674927327948, 4247927513443586, 4247927513443586, 5209453365628950, 5209453365628950,
    10183635381473219, 5209453365628950, 29591756580636139, 1584962500724866, 24069552119163657, 31965218910289295,
    31747665133324320, 30438493292517007, 27065841093136900, 27802806687987110, 32738266435282032, 27802806687987110,
    27065841093136900, 36740033361463166, 32775499341696108, 31965218910289295, 32738266435282032, 27802806687987110,
    32775499341696108, 27802806687987110, 32738266435282032, 27802806687987110, 24069552119163657, 24424345015535906,
    32056139320204539, 32056139320204539, 24424345015535906, 25848668759657764, 31205171265101290, 35569097447810268,
    31205171265101290, 25848668759657764, 29492172698326660, 26679332237229289, 31836281226316625, 30175758063304617,
    26679332237229289, 32836280882218178, 26679332237229289, 26679332237229289, 32052881024306896, 24719974221797463,
    30175758063304617, 32052881024306896, 29492172698326660, 26679332237229289, 24719974221797463, 26679332237229289,
    20580441682918281, 25936944198394613, 30300870372753804, 25936944198394613
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
noncomputable def negativeCeiling : ℝ := 2073971 / 2000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1865675423673848081340694528, coefficient := (-1865675423673848081340694528) }, { argument := 10765181539659797535989432320, coefficient := (-10765181539659797535989432320) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 24874857664390609898754277376, coefficient := (-24874857664390609898754277376) }, { argument := 44991383302778039365865046016, coefficient := (-44991383302778039365865046016) }, { argument := 10765181539659797535989432320, coefficient := (-10765181539659797535989432320) }, { argument := 24874857664390609898754277376, coefficient := (-24874857664390609898754277376) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 44991383302778039365865046016, coefficient := (-44991383302778039365865046016) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1865675423673848081340694528, coefficient := (-1865675423673848081340694528) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 2598165906218622602283319296, coefficient := (-2598165906218622602283319296) }, { argument := 38670468418158929972922679296, coefficient := (-38670468418158929972922679296) }, { argument := 66514942480401801388398477312, coefficient := (-66514942480401801388398477312) }, { argument := 13421134562608107061090713600, coefficient := (-13421134562608107061090713600) }, { argument := 41463860247523200865495154688, coefficient := (-41463860247523200865495154688) }, { argument := 2159576054558500045077872640, coefficient := (-2159576054558500045077872640) }, { argument := 66083027269490101379382902784, coefficient := (-66083027269490101379382902784) }, { argument := 69106433745872001442491924480, coefficient := (-69106433745872001442491924480) }, { argument := 41463860247523200865495154688, coefficient := (-41463860247523200865495154688) }, { argument := 1058624181944576722097173168128, coefficient := (-1058624181944576722097173168128) }, { argument := 67810688113136901415445200896, coefficient := (-67810688113136901415445200896) }, { argument := 38670468418158929972922679296, coefficient := (-38670468418158929972922679296) }, { argument := 66083027269490101379382902784, coefficient := (-66083027269490101379382902784) }, { argument := 2159576054558500045077872640, coefficient := (-2159576054558500045077872640) }, { argument := 67810688113136901415445200896, coefficient := (-67810688113136901415445200896) }, { argument := 2159576054558500045077872640, coefficient := (-2159576054558500045077872640) }, { argument := 66083027269490101379382902784, coefficient := (-66083027269490101379382902784) }, { argument := 69106433745872001442491924480, coefficient := (-69106433745872001442491924480) }, { argument := 2598165906218622602283319296, coefficient := (-2598165906218622602283319296) }, { argument := 51914683375855837181378560, coefficient := (-51914683375855837181378560) }, { argument := 10296490332525369898303488000, coefficient := (-10296490332525369898303488000) }, { argument := 10296490332525369898303488000, coefficient := (-10296490332525369898303488000) }, { argument := 51914683375855837181378560, coefficient := (-51914683375855837181378560) }, { argument := 139333125623320693463580672, coefficient := (-139333125623320693463580672) }, { argument := 22834015812056484311350640640, coefficient := (-22834015812056484311350640640) }, { argument := 235085033855535546459268055040, coefficient := (-235085033855535546459268055040) }, { argument := 22834015812056484311350640640, coefficient := (-22834015812056484311350640640) }, { argument := 139333125623320693463580672, coefficient := (-139333125623320693463580672) }, { argument := 3482477752598748353901101056, coefficient := (-3482477752598748353901101056) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 70728642319728659003686780928, coefficient := (-70728642319728659003686780928) }, { argument := 22373196729897082132679884800, coefficient := (-22373196729897082132679884800) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 70728625450181203596301828096, coefficient := (-70728625450181203596301828096) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 82186097354634597910173450240, coefficient := (-82186097354634597910173450240) }, { argument := 2039076157661506219687280640, coefficient := (-2039076157661506219687280640) }, { argument := 22373196729897082132679884800, coefficient := (-22373196729897082132679884800) }, { argument := 82186097354634597910173450240, coefficient := (-82186097354634597910173450240) }, { argument := 3482477752598748353901101056, coefficient := (-3482477752598748353901101056) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 2039076157661506219687280640, coefficient := (-2039076157661506219687280640) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 7230860810791093872361472, coefficient := (-7230860810791093872361472) }, { argument := 1184998824577781620948336640, coefficient := (-1184998824577781620948336640) }, { argument := 12200021717053740934013911040, coefficient := (-12200021717053740934013911040) }, { argument := 1184998824577781620948336640, coefficient := (-1184998824577781620948336640) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1058580326010944901490781489987584)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1567943, 422707565, 4224942505, 8449882945, 422707565, 275003949,
    60426111, 1567943, 4061559031, 97333077, 1100137145, 97333077,
    101433851, 60426111, 3015275, 809107739, 4668653285, 37,
    3, 643, 1163, 4668653285, 643, 19,
    19, 37, 37, 1163, 37, 809107739,
    3, 4159035853, 35008580789, 26270003529, 14137055975, 1023506631,
    1705844385, 52198838181, 1705844385, 1023506631, 836204917527, 53563513689,
    35008580789, 52198838181, 1705844385, 53563513689, 1705844385, 52198838181,
    1705844385, 4159035853, 7792194825, 1074137925, 3652068945, 12122413725,
    1074137925, 7304137005, 1074137925, 1074137925, 44530689405, 276206895,
    12122413725, 44530689405, 7792194825, 1074137925
  ]
def negativeCoefficients : Array ℕ := #[
    7230860810791093872361472, 1949394567393986270210293760, 77936433115872337646929838080, 77936414069609081541817794560, 1949394567393986270210293760, 2536463733231236886709665792,
    139333125623320693463580672, 7230860810791093872361472, 9365317498140094879615680512, 224434795165708182884450304, 2536743544974561959257047040, 224434795165708182884450304,
    233890536225973459486769152, 139333125623320693463580672, 6952750779606821031116800, 1865675423673848081340694528, 10765181539659797535989432320, 1431368170423720942852112384,
    1856910058928070412348686336, 24874857664390609898754277376, 44991383302778039365865046016, 10765181539659797535989432320, 24874857664390609898754277376, 1470053796651389076442710016,
    1470053796651389076442710016, 1431368170423720942852112384, 1431368170423720942852112384, 44991383302778039365865046016, 1431368170423720942852112384, 1865675423673848081340694528,
    1856910058928070412348686336, 9590083746709162484937261056, 161448582549616952167425376256, 242298015957454878536663826432, 260782653526531457087543705600, 151042919038413430776102125568,
    7866818699917366186255319040, 240724652217471405299412762624, 251738198397355717960170209280, 151042919038413430776102125568, 3856314526699492904502357393408, 247018107177405298248417017856,
    161448582549616952167425376256, 240724652217471405299412762624, 7866818699917366186255319040, 247018107177405298248417017856, 7866818699917366186255319040, 240724652217471405299412762624,
    251738198397355717960170209280, 9590083746709162484937261056, 71870311854629493327632793600, 79257389609361699301962547200, 134737562335914888813336330240, 894476254162796320693577318400,
    79257389609361699301962547200, 134737546010546383580383150080, 79257389609361699301962547200, 79257389609361699301962547200, 3285784923519537876775647313920, 81521886455343462139161477120,
    894476254162796320693577318400, 3285784923519537876775647313920, 71870311854629493327632793600, 79257389609361699301962547200
  ]
def negativeScales : Array ℕ := #[
    20, 28, 31, 32, 28, 28,
    25, 20, 31, 26, 30, 26,
    26, 25, 21, 29, 32, 5,
    1, 9, 10, 32, 9, 4,
    4, 5, 5, 10, 5, 29,
    1, 31, 35, 34, 33, 29,
    30, 35, 30, 29, 39, 35,
    35, 35, 30, 35, 30, 35,
    30, 31, 32, 30, 31, 33,
    30, 32, 30, 30, 35, 28,
    33, 35, 32, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20580441682918281, 28655084690962677, 31976284578782611, 32976284226213741, 28655084690962677, 28034877094688236,
    25848668759657764, 20580441682918281, 31919386472913488, 26536426828052586, 30035036237807273, 26536426828052586,
    26595963955034128, 25848668759657764, 21523858154549244, 29591756580636139, 32120359305581071, 5209453365628950,
    1584962500724866, 9328674927327948, 10183635381473219, 32120359305581071, 9328674927327948, 4247927513443586,
    4247927513443586, 5209453365628950, 5209453365628950, 10183635381473219, 5209453365628950, 29591756580636139,
    1584962500724866, 31953601986863969, 35026989526487724, 34612697343158672, 33718762660894620, 29930873310696250,
    30667838897376458, 35603298645154612, 30667838897376458, 29930873310696250, 39605065571329108, 35640531551364107,
    35026989526487724, 35603298645154612, 30667838897376458, 35640531551364107, 30667838897376458, 35603298645154612,
    30667838897376458, 31953601986863969, 32859382605029992, 30000532108890301, 31766066855571492, 33496957935010044,
    30000532108890301, 32766066680768494, 30000532108890301, 30000532108890301, 35374080896012081, 28041174093387647,
    33496957935010044, 35374080896012081, 32859382605029992, 30000532108890301
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
noncomputable def negativeCeiling : ℝ := 1740002767 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7230860810791093872361472, coefficient := (-7230860810791093872361472) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 77936433115872337646929838080, coefficient := (-77936433115872337646929838080) }, { argument := 77936414069609081541817794560, coefficient := (-77936414069609081541817794560) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 2536463733231236886709665792, coefficient := (-2536463733231236886709665792) }, { argument := 139333125623320693463580672, coefficient := (-139333125623320693463580672) }, { argument := 7230860810791093872361472, coefficient := (-7230860810791093872361472) }, { argument := 9365317498140094879615680512, coefficient := (-9365317498140094879615680512) }, { argument := 224434795165708182884450304, coefficient := (-224434795165708182884450304) }, { argument := 2536743544974561959257047040, coefficient := (-2536743544974561959257047040) }, { argument := 224434795165708182884450304, coefficient := (-224434795165708182884450304) }, { argument := 233890536225973459486769152, coefficient := (-233890536225973459486769152) }, { argument := 139333125623320693463580672, coefficient := (-139333125623320693463580672) }, { argument := 6952750779606821031116800, coefficient := (-6952750779606821031116800) }, { argument := 1865675423673848081340694528, coefficient := (-1865675423673848081340694528) }, { argument := 10765181539659797535989432320, coefficient := (-10765181539659797535989432320) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 24874857664390609898754277376, coefficient := (-24874857664390609898754277376) }, { argument := 44991383302778039365865046016, coefficient := (-44991383302778039365865046016) }, { argument := 10765181539659797535989432320, coefficient := (-10765181539659797535989432320) }, { argument := 24874857664390609898754277376, coefficient := (-24874857664390609898754277376) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 44991383302778039365865046016, coefficient := (-44991383302778039365865046016) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1865675423673848081340694528, coefficient := (-1865675423673848081340694528) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 9590083746709162484937261056, coefficient := (-9590083746709162484937261056) }, { argument := 161448582549616952167425376256, coefficient := (-161448582549616952167425376256) }, { argument := 242298015957454878536663826432, coefficient := (-242298015957454878536663826432) }, { argument := 260782653526531457087543705600, coefficient := (-260782653526531457087543705600) }, { argument := 151042919038413430776102125568, coefficient := (-151042919038413430776102125568) }, { argument := 7866818699917366186255319040, coefficient := (-7866818699917366186255319040) }, { argument := 240724652217471405299412762624, coefficient := (-240724652217471405299412762624) }, { argument := 251738198397355717960170209280, coefficient := (-251738198397355717960170209280) }, { argument := 151042919038413430776102125568, coefficient := (-151042919038413430776102125568) }, { argument := 3856314526699492904502357393408, coefficient := (-3856314526699492904502357393408) }, { argument := 247018107177405298248417017856, coefficient := (-247018107177405298248417017856) }, { argument := 161448582549616952167425376256, coefficient := (-161448582549616952167425376256) }, { argument := 240724652217471405299412762624, coefficient := (-240724652217471405299412762624) }, { argument := 7866818699917366186255319040, coefficient := (-7866818699917366186255319040) }, { argument := 247018107177405298248417017856, coefficient := (-247018107177405298248417017856) }, { argument := 7866818699917366186255319040, coefficient := (-7866818699917366186255319040) }, { argument := 240724652217471405299412762624, coefficient := (-240724652217471405299412762624) }, { argument := 251738198397355717960170209280, coefficient := (-251738198397355717960170209280) }, { argument := 9590083746709162484937261056, coefficient := (-9590083746709162484937261056) }, { argument := 71870311854629493327632793600, coefficient := (-71870311854629493327632793600) }, { argument := 79257389609361699301962547200, coefficient := (-79257389609361699301962547200) }, { argument := 134737562335914888813336330240, coefficient := (-134737562335914888813336330240) }, { argument := 894476254162796320693577318400, coefficient := (-894476254162796320693577318400) }, { argument := 79257389609361699301962547200, coefficient := (-79257389609361699301962547200) }, { argument := 134737546010546383580383150080, coefficient := (-134737546010546383580383150080) }, { argument := 79257389609361699301962547200, coefficient := (-79257389609361699301962547200) }, { argument := 79257389609361699301962547200, coefficient := (-79257389609361699301962547200) }, { argument := 3285784923519537876775647313920, coefficient := (-3285784923519537876775647313920) }, { argument := 81521886455343462139161477120, coefficient := (-81521886455343462139161477120) }, { argument := 894476254162796320693577318400, coefficient := (-894476254162796320693577318400) }, { argument := 3285784923519537876775647313920, coefficient := (-3285784923519537876775647313920) }, { argument := 71870311854629493327632793600, coefficient := (-71870311854629493327632793600) }, { argument := 79257389609361699301962547200, coefficient := (-79257389609361699301962547200) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
