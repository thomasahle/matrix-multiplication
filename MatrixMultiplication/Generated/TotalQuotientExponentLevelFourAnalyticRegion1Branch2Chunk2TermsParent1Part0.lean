import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 2, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2

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
def constantNumerator : ℤ := (-55683715566401585469709065650176)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    62085, 4588111, 153, 42411605, 157, 5,
    153, 87, 157, 2451, 3, 2294057,
    153, 5, 3, 5, 77, 87,
    62085, 2402526845, 1183061205, 42728662805, 29274471945, 931346055,
    42728683305, 478258785, 478258785, 16185284145, 881003025, 29274471945,
    16185284145, 2402516595, 931346055, 881003025, 1183061205, 35990535,
    110293575, 35990535, 6900812181, 363388305, 575848467, 727937595,
    326236785, 110293575, 35990535, 593068985, 10377967915, 10377973005,
    593063895, 110293575, 3016809645, 882348315, 2402526845, 593068985,
    2401980509, 299447405, 35990535, 984432621, 287924187, 1183061205,
    1182526251, 62085, 2401980509, 1182526251
  ]
def negativeCoefficients : Array ℕ := #[
    293188123088961923092316160, 21666741606085530771055968256, 2959450406416612219680718848, 200283141936706659293415342080, 3036821658871948486861914112, 96714065569170333976494080,
    2959450406416612219680718848, 1682824740903563811190996992, 3036821658871948486861914112, 47409234942007297715277398016, 1856910058928070412348686336, 21666755773184979379991609344,
    2959450406416612219680718848, 96714065569170333976494080, 1856910058928070412348686336, 96714065569170333976494080, 2978793219530446286476017664, 1682824740903563811190996992,
    293188123088961923092316160, 2769924864995741030647070720, 1363976704510589434677166080, 49262794210979218531737927680, 33751168241400330053820088320, 1073768895040251257086279680,
    49262817845870062972100935680, 1102789675987285074845368320, 1102789675987285074845368320, 18660362148942744819093995520, 1015727333146183621568102400, 33751168241400330053820088320,
    18660362148942744819093995520, 2769913047550318810465566720, 1073768895040251257086279680, 1015727333146183621568102400, 1363976704510589434677166080, 1327816376441772394539909120,
    16276458807995919675005337600, 663908188220886197269954560, 15912189525455554455967629312, 13406662123428218048096501760, 1327816161998372537666371584, 13428078516596633731879403520,
    12036012960649614285990789120, 16276458807995919675005337600, 663908188220886197269954560, 1367523973043711120213278720, 47859929533293530424971100160, 47859953006775364220375531520,
    1367512236302794222511063040, 16276458807995919675005337600, 55650315440413566243774136320, 16276453550673858667783127040, 2769924864995741030647070720, 1367523973043711120213278720,
    2769294982472600144297590784, 1380957410892863488781189120, 663908188220886197269954560, 2269947077174763886259208192, 663907973777486340396417024, 1363976704510589434677166080,
    1363359944540013983459966976, 293188123088961923092316160, 2769294982472600144297590784, 1363359944540013983459966976
  ]
def negativeScales : Array ℕ := #[
    15, 22, 7, 25, 7, 2,
    7, 6, 7, 11, 1, 21,
    7, 2, 1, 2, 6, 6,
    15, 31, 30, 35, 34, 29,
    35, 28, 28, 33, 29, 34,
    33, 31, 29, 29, 30, 25,
    26, 25, 32, 28, 29, 29,
    28, 26, 25, 29, 33, 33,
    29, 26, 31, 29, 31, 29,
    31, 28, 25, 29, 28, 30,
    30, 15, 31, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15921957135279622, 22129468864167974, 7257387842692652, 25337955744687181, 7294620748891628, 2321928094887363,
    7257387842692652, 6442943495848765, 7294620748891628, 11259154768866840, 1584962500724866, 21129469807493824,
    7257387842692652, 2321928094887363, 1584962500724866, 2321928094887363, 6266786540694902, 6442943495848765,
    15921957135279622, 31161905405248346, 30139877566603827, 35314485117407240, 34768924096737609, 29794742081135281,
    35314485809571218, 28833216229622703, 28833216229622703, 33913963647852301, 29714571731972760, 34768924096737609,
    33913963647852301, 31161899250205482, 29794742081135281, 29714571731972760, 30139877566603827, 25101114212323306,
    26716773510374255, 25101114212323306, 32684119021802866, 28436936748869077, 29101113979326891, 29439239534738500,
    28281344222157357, 26716773510374255, 25101114212323306, 29143624686009981, 33272804929567882, 33272805637154956,
    29143612304062086, 26716773510374255, 31490376522006220, 29716773044381387, 31161905405248346, 29143624686009981,
    31161577298250820, 28157727389128163, 25101114212323306, 29874717226818002, 28101113746330440, 30139877566603827,
    30139225064415331, 15921957135279622, 31161577298250820, 30139225064415331
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
noncomputable def negativeCeiling : ℝ := 140605031 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 293188123088961923092316160, coefficient := (-293188123088961923092316160) }, { argument := 21666741606085530771055968256, coefficient := (-21666741606085530771055968256) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 200283141936706659293415342080, coefficient := (-200283141936706659293415342080) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 47409234942007297715277398016, coefficient := (-47409234942007297715277398016) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 21666755773184979379991609344, coefficient := (-21666755773184979379991609344) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 2978793219530446286476017664, coefficient := (-2978793219530446286476017664) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 293188123088961923092316160, coefficient := (-293188123088961923092316160) }, { argument := 2769924864995741030647070720, coefficient := (-2769924864995741030647070720) }, { argument := 1363976704510589434677166080, coefficient := (-1363976704510589434677166080) }, { argument := 49262794210979218531737927680, coefficient := (-49262794210979218531737927680) }, { argument := 33751168241400330053820088320, coefficient := (-33751168241400330053820088320) }, { argument := 1073768895040251257086279680, coefficient := (-1073768895040251257086279680) }, { argument := 49262817845870062972100935680, coefficient := (-49262817845870062972100935680) }, { argument := 1102789675987285074845368320, coefficient := (-1102789675987285074845368320) }, { argument := 1102789675987285074845368320, coefficient := (-1102789675987285074845368320) }, { argument := 18660362148942744819093995520, coefficient := (-18660362148942744819093995520) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 33751168241400330053820088320, coefficient := (-33751168241400330053820088320) }, { argument := 18660362148942744819093995520, coefficient := (-18660362148942744819093995520) }, { argument := 2769913047550318810465566720, coefficient := (-2769913047550318810465566720) }, { argument := 1073768895040251257086279680, coefficient := (-1073768895040251257086279680) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 1363976704510589434677166080, coefficient := (-1363976704510589434677166080) }, { argument := 1327816376441772394539909120, coefficient := (-1327816376441772394539909120) }, { argument := 16276458807995919675005337600, coefficient := (-16276458807995919675005337600) }, { argument := 663908188220886197269954560, coefficient := (-663908188220886197269954560) }, { argument := 15912189525455554455967629312, coefficient := (-15912189525455554455967629312) }, { argument := 13406662123428218048096501760, coefficient := (-13406662123428218048096501760) }, { argument := 1327816161998372537666371584, coefficient := (-1327816161998372537666371584) }, { argument := 13428078516596633731879403520, coefficient := (-13428078516596633731879403520) }, { argument := 12036012960649614285990789120, coefficient := (-12036012960649614285990789120) }, { argument := 16276458807995919675005337600, coefficient := (-16276458807995919675005337600) }, { argument := 663908188220886197269954560, coefficient := (-663908188220886197269954560) }, { argument := 1367523973043711120213278720, coefficient := (-1367523973043711120213278720) }, { argument := 47859929533293530424971100160, coefficient := (-47859929533293530424971100160) }, { argument := 47859953006775364220375531520, coefficient := (-47859953006775364220375531520) }, { argument := 1367512236302794222511063040, coefficient := (-1367512236302794222511063040) }, { argument := 16276458807995919675005337600, coefficient := (-16276458807995919675005337600) }, { argument := 55650315440413566243774136320, coefficient := (-55650315440413566243774136320) }, { argument := 16276453550673858667783127040, coefficient := (-16276453550673858667783127040) }, { argument := 2769924864995741030647070720, coefficient := (-2769924864995741030647070720) }, { argument := 1367523973043711120213278720, coefficient := (-1367523973043711120213278720) }, { argument := 2769294982472600144297590784, coefficient := (-2769294982472600144297590784) }, { argument := 1380957410892863488781189120, coefficient := (-1380957410892863488781189120) }, { argument := 663908188220886197269954560, coefficient := (-663908188220886197269954560) }, { argument := 2269947077174763886259208192, coefficient := (-2269947077174763886259208192) }, { argument := 663907973777486340396417024, coefficient := (-663907973777486340396417024) }, { argument := 1363976704510589434677166080, coefficient := (-1363976704510589434677166080) }, { argument := 1363359944540013983459966976, coefficient := (-1363359944540013983459966976) }, { argument := 293188123088961923092316160, coefficient := (-293188123088961923092316160) }, { argument := 2769294982472600144297590784, coefficient := (-2769294982472600144297590784) }, { argument := 1363359944540013983459966976, coefficient := (-1363359944540013983459966976) }] }

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
def constantNumerator : ℤ := (-101880921493435138473576162656256)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    42728241671, 29261234679, 930924921, 42728262171, 478042527, 478042527,
    16177965519, 880604655, 29261234679, 16177965519, 2401970259, 930924921,
    880604655, 1182526251, 6900812181, 3016809645, 984432621, 20228502567,
    9939593883, 3450405135, 19910943657, 8923405371, 3016809645, 984432621,
    42728662805, 10377967915, 42728241671, 5239956295, 363388305, 9939593883,
    2907105501, 29274471945, 29261234679, 4588111, 931346055, 930924921,
    153, 575848467, 882348315, 287924187, 3450405135, 2907105501,
    287924187, 5823498879, 2609893437, 882348315, 287924187, 42728683305,
    10377973005, 42728262171, 5239958865, 42411605, 478258785, 478042527,
    157, 5, 299447405, 5239956295, 5239958865, 299444835,
    727937595, 19910943657, 5823498879, 478258785
  ]
def negativeCoefficients : Array ℕ := #[
    49262308676534297431843536896, 33735906712766728994977480704, 1073283360595330157191888896, 49262332311425141872206544896, 1102291018989798539818696704, 1102291018989798539818696704,
    18651924347643170029037420544, 1015268043806393391938273280, 33735906712766728994977480704, 18651924347643170029037420544, 2769283165027177924116086784, 1073283360595330157191888896,
    1015268043806393391938273280, 1363359944540013983459966976, 15912189525455554455967629312, 55650315440413566243774136320, 2269947077174763886259208192, 93287502461956425519168749568,
    45838286139077490090266591232, 15912185118989563848598487040, 45911510238341192151113662464, 41151943786200558196054032384, 55650315440413566243774136320, 2269947077174763886259208192,
    49262794210979218531737927680, 47859929533293530424971100160, 49262308676534297431843536896, 48330066365644154495943311360, 13406662123428218048096501760, 45838286139077490090266591232,
    13406657793055046744779259904, 33751168241400330053820088320, 33735906712766728994977480704, 21666741606085530771055968256, 1073768895040251257086279680, 1073283360595330157191888896,
    2959450406416612219680718848, 1327816161998372537666371584, 16276453550673858667783127040, 663907973777486340396417024, 15912185118989563848598487040, 13406657793055046744779259904,
    1327815947554972680792834048, 13428074179305933400921079808, 12036009072998300751702786048, 16276453550673858667783127040, 663907973777486340396417024, 49262817845870062972100935680,
    47859953006775364220375531520, 49262332311425141872206544896, 48330090069710289212717137920, 200283141936706659293415342080, 1102789675987285074845368320, 1102291018989798539818696704,
    3036821658871948486861914112, 96714065569170333976494080, 1380957410892863488781189120, 48330066365644154495943311360, 48330090069710289212717137920, 1380945558859796130394275840,
    13428078516596633731879403520, 45911510238341192151113662464, 13428074179305933400921079808, 1102789675987285074845368320
  ]
def negativeScales : Array ℕ := #[
    35, 34, 29, 35, 28, 28,
    33, 29, 34, 33, 31, 29,
    29, 30, 32, 31, 29, 34,
    33, 31, 34, 33, 31, 29,
    35, 33, 35, 32, 28, 33,
    31, 34, 34, 22, 29, 29,
    7, 29, 29, 28, 31, 31,
    28, 32, 31, 29, 28, 35,
    33, 35, 32, 25, 28, 28,
    7, 2, 28, 32, 32, 28,
    29, 34, 32, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35314470898124735, 34768271594544448, 29794089578939061, 35314471590295536, 28832563727418353, 28832563727418353,
    33913311145599764, 29713919229782749, 34768271594544448, 33913311145599764, 31161571141807974, 29794089578939061,
    29713919229782749, 30139225064415331, 32684119021802866, 31490376522006220, 29874717226818002, 34235670475931377,
    33210539760607695, 31684118622286036, 34212842546477115, 33054947233896002, 31490376522006220, 29874717226818002,
    35314485117407240, 33272804929567882, 35314470898124735, 32286907632686065, 28436936748869077, 33210539760607695,
    31436936282876211, 34768924096737609, 34768271594544448, 22129468864167974, 29794742081135281, 29794089578939061,
    7257387842692652, 29101113979326891, 29716773044381387, 28101113746330440, 31684118622286036, 31436936282876211,
    28101113746330440, 32439239068745634, 31281343756164491, 29716773044381387, 28101113746330440, 35314485809571218,
    33272805637154956, 35314471590295536, 32286908340273139, 25337955744687181, 28833216229622703, 28832563727418353,
    7294620748891628, 2321928094887363, 28157727389128163, 32286907632686065, 32286908340273139, 28157715007180269,
    29439239534738500, 34212842546477115, 32439239068745634, 28833216229622703
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
noncomputable def negativeCeiling : ℝ := 623874277 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 49262308676534297431843536896, coefficient := (-49262308676534297431843536896) }, { argument := 33735906712766728994977480704, coefficient := (-33735906712766728994977480704) }, { argument := 1073283360595330157191888896, coefficient := (-1073283360595330157191888896) }, { argument := 49262332311425141872206544896, coefficient := (-49262332311425141872206544896) }, { argument := 1102291018989798539818696704, coefficient := (-1102291018989798539818696704) }, { argument := 1102291018989798539818696704, coefficient := (-1102291018989798539818696704) }, { argument := 18651924347643170029037420544, coefficient := (-18651924347643170029037420544) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 33735906712766728994977480704, coefficient := (-33735906712766728994977480704) }, { argument := 18651924347643170029037420544, coefficient := (-18651924347643170029037420544) }, { argument := 2769283165027177924116086784, coefficient := (-2769283165027177924116086784) }, { argument := 1073283360595330157191888896, coefficient := (-1073283360595330157191888896) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 1363359944540013983459966976, coefficient := (-1363359944540013983459966976) }, { argument := 15912189525455554455967629312, coefficient := (-15912189525455554455967629312) }, { argument := 55650315440413566243774136320, coefficient := (-55650315440413566243774136320) }, { argument := 2269947077174763886259208192, coefficient := (-2269947077174763886259208192) }, { argument := 93287502461956425519168749568, coefficient := (-93287502461956425519168749568) }, { argument := 45838286139077490090266591232, coefficient := (-45838286139077490090266591232) }, { argument := 15912185118989563848598487040, coefficient := (-15912185118989563848598487040) }, { argument := 45911510238341192151113662464, coefficient := (-45911510238341192151113662464) }, { argument := 41151943786200558196054032384, coefficient := (-41151943786200558196054032384) }, { argument := 55650315440413566243774136320, coefficient := (-55650315440413566243774136320) }, { argument := 2269947077174763886259208192, coefficient := (-2269947077174763886259208192) }, { argument := 49262794210979218531737927680, coefficient := (-49262794210979218531737927680) }, { argument := 47859929533293530424971100160, coefficient := (-47859929533293530424971100160) }, { argument := 49262308676534297431843536896, coefficient := (-49262308676534297431843536896) }, { argument := 48330066365644154495943311360, coefficient := (-48330066365644154495943311360) }, { argument := 13406662123428218048096501760, coefficient := (-13406662123428218048096501760) }, { argument := 45838286139077490090266591232, coefficient := (-45838286139077490090266591232) }, { argument := 13406657793055046744779259904, coefficient := (-13406657793055046744779259904) }, { argument := 33751168241400330053820088320, coefficient := (-33751168241400330053820088320) }, { argument := 33735906712766728994977480704, coefficient := (-33735906712766728994977480704) }, { argument := 21666741606085530771055968256, coefficient := (-21666741606085530771055968256) }, { argument := 1073768895040251257086279680, coefficient := (-1073768895040251257086279680) }, { argument := 1073283360595330157191888896, coefficient := (-1073283360595330157191888896) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 1327816161998372537666371584, coefficient := (-1327816161998372537666371584) }, { argument := 16276453550673858667783127040, coefficient := (-16276453550673858667783127040) }, { argument := 663907973777486340396417024, coefficient := (-663907973777486340396417024) }, { argument := 15912185118989563848598487040, coefficient := (-15912185118989563848598487040) }, { argument := 13406657793055046744779259904, coefficient := (-13406657793055046744779259904) }, { argument := 1327815947554972680792834048, coefficient := (-1327815947554972680792834048) }, { argument := 13428074179305933400921079808, coefficient := (-13428074179305933400921079808) }, { argument := 12036009072998300751702786048, coefficient := (-12036009072998300751702786048) }, { argument := 16276453550673858667783127040, coefficient := (-16276453550673858667783127040) }, { argument := 663907973777486340396417024, coefficient := (-663907973777486340396417024) }, { argument := 49262817845870062972100935680, coefficient := (-49262817845870062972100935680) }, { argument := 47859953006775364220375531520, coefficient := (-47859953006775364220375531520) }, { argument := 49262332311425141872206544896, coefficient := (-49262332311425141872206544896) }, { argument := 48330090069710289212717137920, coefficient := (-48330090069710289212717137920) }, { argument := 200283141936706659293415342080, coefficient := (-200283141936706659293415342080) }, { argument := 1102789675987285074845368320, coefficient := (-1102789675987285074845368320) }, { argument := 1102291018989798539818696704, coefficient := (-1102291018989798539818696704) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 1380957410892863488781189120, coefficient := (-1380957410892863488781189120) }, { argument := 48330066365644154495943311360, coefficient := (-48330066365644154495943311360) }, { argument := 48330090069710289212717137920, coefficient := (-48330090069710289212717137920) }, { argument := 1380945558859796130394275840, coefficient := (-1380945558859796130394275840) }, { argument := 13428078516596633731879403520, coefficient := (-13428078516596633731879403520) }, { argument := 45911510238341192151113662464, coefficient := (-45911510238341192151113662464) }, { argument := 13428074179305933400921079808, coefficient := (-13428074179305933400921079808) }, { argument := 1102789675987285074845368320, coefficient := (-1102789675987285074845368320) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2
