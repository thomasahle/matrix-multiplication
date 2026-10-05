import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 23, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23

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
def constantNumerator : ℤ := (-35209898713710968339159549214720)
def positiveArguments : Array ℕ := #[
    79, 21, 105, 87, 1563, 585,
    21, 2343, 2343, 1677, 87, 305,
    335, 305, 335, 17, 9, 176160765,
    176160771, 69712093, 127422821, 69706841
  ]
def positiveCoefficients : Array ℕ := #[
    6259024838626882669889972076544, 3249592603124123221610201088, 64991852062482464432204021760, 3365649481807127622381993984, 60465633793845292802104098816, 90524365372743432601998458880,
    3249592603124123221610201088, 90640422251426437002770251776, 90640422251426437002770251776, 64875795183799460031432228864, 3365649481807127622381993984, 188785855991020491922116444160,
    207354956580301196045603307520, 188785855991020491922116444160, 207354956580301196045603307520, 1346878762742493739090247155712, 2852213850513516153367582212096, 1663791384465352192246551674880,
    1663791441133749986682294239232, 658412102867783228028360851456, 2406949036172393473593168625664, 658362499130247165275036188672
  ]
def positiveScales : Array ℕ := #[
    6, 4, 6, 6, 10, 9,
    4, 11, 11, 10, 6, 8,
    8, 8, 8, 4, 3, 27,
    27, 26, 26, 26
  ]
def negativeArguments : Array ℕ := #[
    35762049, 105, 87, 266700725, 585, 71518537,
    2343, 2343, 1677, 87, 11148459313, 2810184015,
    1329, 2810184015, 8573527, 2810184015, 2810183345, 105,
    87, 1329, 2810183345, 11148460751, 2810183345, 255794655,
    585, 68583273, 2810184015, 2810183345, 2343, 2343,
    1677, 87, 3, 5, 17, 9,
    21, 47
  ]
def negativeCoefficients : Array ℕ := #[
    337763003112683825489623646208, 32495926031241232216102010880, 1682824740903563811190996992, 1259458564697034458985503129600, 45262182686371716300999229440, 337736742032672587392590282752,
    45320211125713218501385125888, 45320211125713218501385125888, 32437897591899730015716114432, 1682824740903563811190996992, 411305551526149618340898799616, 51838745324734563704100618240,
    411305578052567596335234023424, 51838745324734563704100618240, 323898692358223525760347406336, 51838745324734563704100618240, 51838732965416034318701035520, 32495926031241232216102010880,
    1682824740903563811190996992, 411305578052567596335234023424, 51838732965416034318701035520, 411305604578985574329569247232, 51838732965416034318701035520, 1207956105269204307409769594880,
    45262182686371716300999229440, 323875349700698701104056107008, 51838745324734563704100618240, 51838732965416034318701035520, 45320211125713218501385125888, 45320211125713218501385125888,
    32437897591899730015716114432, 1682824740903563811190996992, 475368975085586025561263702016, 792281625142643375935439503360, 1346878762742493739090247155712, 2852213850513516153367582212096,
    3327582825599102178928845914112, 3723723638170423866896565665792
  ]
def negativeScales : Array ℕ := #[
    25, 6, 6, 27, 9, 26,
    11, 11, 10, 6, 33, 31,
    10, 31, 23, 31, 31, 6,
    6, 10, 31, 33, 31, 27,
    9, 26, 31, 31, 11, 11,
    10, 6, 1, 2, 4, 3,
    4, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6303780748177102, 4392317422778759, 6714245517659862, 6442943495848725, 10610102062999199, 9192292814470766,
    4392317422778759, 11194141238863135, 11194141238863135, 10711666973558447, 6442943495848725, 8252665432450248,
    8388017285345134, 8252665432450248, 8388017285345134, 4087462841250339, 3169925001442312, 27392317398209809,
    27392317447347709, 26054905607217909, 26925048441258209, 26054796912736593
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    25091926062853916, 6714245517766967, 6442943495848765, 27990646526199381, 9192292814470767, 26091813888925822,
    11194141238863136, 11194141238863136, 10711666973659367, 6442943495848765, 33376125296232137, 31388017457327780,
    10376125389276177, 31388017457327780, 23031457395438963, 31388017457327780, 31388017113362478, 6714245517766967,
    6442943495848765, 10376125389276177, 31388017113362478, 33376125482320212, 31388017113362478, 27930410885017355,
    9192292814470767, 26031353419873163, 31388017457327780, 31388017113362478, 11194141238863136, 11194141238863136,
    10711666973659367, 6442943495848765, 1584962500724866, 2321928094887363, 4087462841250340, 3169925001442313,
    4392317422778766, 5554588851679165
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 38
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
noncomputable def positiveFloor : ℝ := 3076295969 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2499533977 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 337763003112683825489623646208, coefficient := (-337763003112683825489623646208) }, { argument := 32495926031241232216102010880, coefficient := (-32495926031241232216102010880) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 1259458564697034458985503129600, coefficient := (-1259458564697034458985503129600) }, { argument := 45262182686371716300999229440, coefficient := (-45262182686371716300999229440) }, { argument := 337736742032672587392590282752, coefficient := (-337736742032672587392590282752) }, { argument := 45320211125713218501385125888, coefficient := (-45320211125713218501385125888) }, { argument := 45320211125713218501385125888, coefficient := (-45320211125713218501385125888) }, { argument := 32437897591899730015716114432, coefficient := (-32437897591899730015716114432) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 411305551526149618340898799616, coefficient := (-411305551526149618340898799616) }, { argument := 51838745324734563704100618240, coefficient := (-51838745324734563704100618240) }, { argument := 411305578052567596335234023424, coefficient := (-411305578052567596335234023424) }, { argument := 51838745324734563704100618240, coefficient := (-51838745324734563704100618240) }, { argument := 323898692358223525760347406336, coefficient := (-323898692358223525760347406336) }, { argument := 51838745324734563704100618240, coefficient := (-51838745324734563704100618240) }, { argument := 51838732965416034318701035520, coefficient := (-51838732965416034318701035520) }, { argument := 32495926031241232216102010880, coefficient := (-32495926031241232216102010880) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 411305578052567596335234023424, coefficient := (-411305578052567596335234023424) }, { argument := 51838732965416034318701035520, coefficient := (-51838732965416034318701035520) }, { argument := 411305604578985574329569247232, coefficient := (-411305604578985574329569247232) }, { argument := 51838732965416034318701035520, coefficient := (-51838732965416034318701035520) }, { argument := 1207956105269204307409769594880, coefficient := (-1207956105269204307409769594880) }, { argument := 45262182686371716300999229440, coefficient := (-45262182686371716300999229440) }, { argument := 323875349700698701104056107008, coefficient := (-323875349700698701104056107008) }, { argument := 51838745324734563704100618240, coefficient := (-51838745324734563704100618240) }, { argument := 51838732965416034318701035520, coefficient := (-51838732965416034318701035520) }, { argument := 45320211125713218501385125888, coefficient := (-45320211125713218501385125888) }, { argument := 45320211125713218501385125888, coefficient := (-45320211125713218501385125888) }, { argument := 32437897591899730015716114432, coefficient := (-32437897591899730015716114432) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 6259024838626882669889972076544, coefficient := 6259024838626882669889972076544 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 64991852062482464432204021760, coefficient := 64991852062482464432204021760 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 60465633793845292802104098816, coefficient := 60465633793845292802104098816 }, { argument := 90524365372743432601998458880, coefficient := 90524365372743432601998458880 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 90640422251426437002770251776, coefficient := 90640422251426437002770251776 }, { argument := 90640422251426437002770251776, coefficient := 90640422251426437002770251776 }, { argument := 64875795183799460031432228864, coefficient := 64875795183799460031432228864 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 2852213850513516153367582212096, coefficient := (-2852213850513516153367582212096) }, { argument := 1663791384465352192246551674880, coefficient := 1663791384465352192246551674880 }, { argument := 1663791441133749986682294239232, coefficient := 1663791441133749986682294239232 }, { argument := 3327582825599102178928845914112, coefficient := (-3327582825599102178928845914112) }, { argument := 658412102867783228028360851456, coefficient := 658412102867783228028360851456 }, { argument := 2406949036172393473593168625664, coefficient := 2406949036172393473593168625664 }, { argument := 658362499130247165275036188672, coefficient := 658362499130247165275036188672 }, { argument := 3723723638170423866896565665792, coefficient := (-3723723638170423866896565665792) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23
