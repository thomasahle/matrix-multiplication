import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 229558494817250128975159615291392
def positiveArguments : Array ℕ := #[
    9, 1, 46163515, 2545, 46152133, 1285,
    1208601, 285, 93, 39583347, 939, 9668805,
    1881, 843, 285, 93, 1754989, 141,
    20616263, 3489
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 633825300114114700748351602688, 436002071934900219734267002880, 196909837498830799976141946880, 435894571984284175130622427136, 198844118810214206655671828480,
    182638619314007554397382377472, 176406455598166689173125201920, 7195526478346272847851159552, 747708284610394889042471682048, 145303212111121509766284705792, 182638562645609759961639813120,
    145535325868487518567828291584, 130447931639696946467495215104, 176406455598166689173125201920, 7195526478346272847851159552, 16575402462809831567878258688, 5454673298101206836274266112,
    389430197572902401768991752192, 134974149908334118097595138048
  ]
def positiveScales : Array ℕ := #[
    3, 0, 25, 11, 25, 10,
    20, 8, 6, 25, 9, 23,
    10, 9, 8, 6, 20, 7,
    24, 11
  ]
def negativeArguments : Array ℕ := #[
    478042527, 326236785, 8923405371, 2609893437, 16185284145, 16177965519,
    153, 881003025, 880604655, 87, 110293575, 3016809645,
    882348315, 29274471945, 29261234679, 157, 16185284145, 16177965519,
    2451, 3, 2402516595, 593063895, 2401970259, 299444835,
    2294057, 153, 35990535, 984432621, 287924187, 931346055,
    930924921, 5, 881003025, 880604655, 3, 5,
    1183061205, 1182526251, 77, 87, 62085, 1,
    1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    1102291018989798539818696704, 12036012960649614285990789120, 41151943786200558196054032384, 12036009072998300751702786048, 18660362148942744819093995520, 18651924347643170029037420544,
    2959450406416612219680718848, 1015727333146183621568102400, 1015268043806393391938273280, 1682824740903563811190996992, 16276458807995919675005337600, 55650315440413566243774136320,
    16276453550673858667783127040, 33751168241400330053820088320, 33735906712766728994977480704, 3036821658871948486861914112, 18660362148942744819093995520, 18651924347643170029037420544,
    47409234942007297715277398016, 1856910058928070412348686336, 2769913047550318810465566720, 1367512236302794222511063040, 2769283165027177924116086784, 1380945558859796130394275840,
    21666755773184979379991609344, 2959450406416612219680718848, 663908188220886197269954560, 2269947077174763886259208192, 663907973777486340396417024, 1073768895040251257086279680,
    1073283360595330157191888896, 96714065569170333976494080, 1015727333146183621568102400, 1015268043806393391938273280, 1856910058928070412348686336, 96714065569170333976494080,
    1363976704510589434677166080, 1363359944540013983459966976, 2978793219530446286476017664, 1682824740903563811190996992, 293188123088961923092316160, 633825300114114700748351602688,
    1267650600228229401496703205376, 1901475900342344102245054808064
  ]
def negativeScales : Array ℕ := #[
    28, 28, 33, 31, 33, 33,
    7, 29, 29, 6, 26, 31,
    29, 34, 34, 7, 33, 33,
    11, 1, 31, 29, 31, 28,
    21, 7, 25, 29, 28, 29,
    29, 2, 29, 29, 1, 2,
    30, 30, 6, 6, 15, 0,
    0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 0, 25460249742614381, 11313449940963057, 25459893990249656, 10327552644081240,
    20204906610164983, 8154818109052103, 6539158811107971, 25238390269930687, 9874981347482478, 23204906162531128,
    10877284133344468, 9719388820935039, 8154818109052103, 6539158811107971, 20743030557280681, 7139551352398793,
    24297279510983074, 11768597882173550
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    28832563727418353, 28281344222157357, 33054947233896002, 31281343756164491, 33913963647852301, 33913311145599764,
    7257387842692652, 29714571731972760, 29713919229782749, 6442943495848765, 26716773510374255, 31490376522006220,
    29716773044381387, 34768924096737609, 34768271594544448, 7294620748891628, 33913963647852301, 33913311145599764,
    11259154768866840, 1584962500724866, 31161899250205482, 29143612304062086, 31161571141807974, 28157715007180269,
    21129469807493824, 7257387842692652, 25101114212323306, 29874717226818002, 28101113746330440, 29794742081135281,
    29794089578939061, 2321928094887363, 29714571731972760, 29713919229782749, 1584962500724866, 2321928094887363,
    30139877566603827, 30139225064415331, 6266786540694902, 6442943495848765, 15921957135279622, 0,
    0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 44
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
noncomputable def positiveFloor : ℝ := 487565641 / 500000000000
noncomputable def negativeCeiling : ℝ := 173337851 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1102291018989798539818696704, coefficient := (-1102291018989798539818696704) }, { argument := 12036012960649614285990789120, coefficient := (-12036012960649614285990789120) }, { argument := 41151943786200558196054032384, coefficient := (-41151943786200558196054032384) }, { argument := 12036009072998300751702786048, coefficient := (-12036009072998300751702786048) }, { argument := 18660362148942744819093995520, coefficient := (-18660362148942744819093995520) }, { argument := 18651924347643170029037420544, coefficient := (-18651924347643170029037420544) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 16276458807995919675005337600, coefficient := (-16276458807995919675005337600) }, { argument := 55650315440413566243774136320, coefficient := (-55650315440413566243774136320) }, { argument := 16276453550673858667783127040, coefficient := (-16276453550673858667783127040) }, { argument := 33751168241400330053820088320, coefficient := (-33751168241400330053820088320) }, { argument := 33735906712766728994977480704, coefficient := (-33735906712766728994977480704) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 18660362148942744819093995520, coefficient := (-18660362148942744819093995520) }, { argument := 18651924347643170029037420544, coefficient := (-18651924347643170029037420544) }, { argument := 47409234942007297715277398016, coefficient := (-47409234942007297715277398016) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 2769913047550318810465566720, coefficient := (-2769913047550318810465566720) }, { argument := 1367512236302794222511063040, coefficient := (-1367512236302794222511063040) }, { argument := 2769283165027177924116086784, coefficient := (-2769283165027177924116086784) }, { argument := 1380945558859796130394275840, coefficient := (-1380945558859796130394275840) }, { argument := 21666755773184979379991609344, coefficient := (-21666755773184979379991609344) }, { argument := 2959450406416612219680718848, coefficient := (-2959450406416612219680718848) }, { argument := 663908188220886197269954560, coefficient := (-663908188220886197269954560) }, { argument := 2269947077174763886259208192, coefficient := (-2269947077174763886259208192) }, { argument := 663907973777486340396417024, coefficient := (-663907973777486340396417024) }, { argument := 1073768895040251257086279680, coefficient := (-1073768895040251257086279680) }, { argument := 1073283360595330157191888896, coefficient := (-1073283360595330157191888896) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 1015727333146183621568102400, coefficient := (-1015727333146183621568102400) }, { argument := 1015268043806393391938273280, coefficient := (-1015268043806393391938273280) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 96714065569170333976494080, coefficient := (-96714065569170333976494080) }, { argument := 1363976704510589434677166080, coefficient := (-1363976704510589434677166080) }, { argument := 1363359944540013983459966976, coefficient := (-1363359944540013983459966976) }, { argument := 2978793219530446286476017664, coefficient := (-2978793219530446286476017664) }, { argument := 1682824740903563811190996992, coefficient := (-1682824740903563811190996992) }, { argument := 293188123088961923092316160, coefficient := (-293188123088961923092316160) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 436002071934900219734267002880, coefficient := 436002071934900219734267002880 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 435894571984284175130622427136, coefficient := 435894571984284175130622427136 }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 182638619314007554397382377472, coefficient := 182638619314007554397382377472 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 747708284610394889042471682048, coefficient := 747708284610394889042471682048 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 182638562645609759961639813120, coefficient := 182638562645609759961639813120 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 16575402462809831567878258688, coefficient := 16575402462809831567878258688 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 389430197572902401768991752192, coefficient := 389430197572902401768991752192 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-84583499879480351903079787921408)
def positiveArguments : Array ℕ := #[
    111, 20616273, 57, 57, 1929, 105,
    3489, 1929, 1754979, 111, 105, 141,
    62085, 4588111, 153, 42411605, 157, 5,
    153, 87, 157, 2451, 3, 2294057,
    153, 5, 3, 5, 77, 87,
    62085
  ]
def positiveCoefficients : Array ℕ := #[
    4294104511271162828556337152, 389430386467561716554800300032, 4410161389954167229328130048, 4410161389954167229328130048, 74624572993171829696262832128, 4061990753905154027012751360,
    134974149908334118097595138048, 74624572993171829696262832128, 16575308015480174174973984768, 4294104511271162828556337152, 4061990753905154027012751360, 5454673298101206836274266112,
    586376246177923846184632320, 43333483212171061542111936512, 5918900812833224439361437696, 400566283873413318586830684160, 6073643317743896973723828224, 193428131138340667952988160,
    5918900812833224439361437696, 3365649481807127622381993984, 6073643317743896973723828224, 94818469884014595430554796032, 3713820117856140824697372672, 43333511546369958759983218688,
    5918900812833224439361437696, 193428131138340667952988160, 3713820117856140824697372672, 193428131138340667952988160, 5957586439060892572952035328, 3365649481807127622381993984,
    586376246177923846184632320
  ]
def positiveScales : Array ℕ := #[
    6, 24, 5, 5, 10, 6,
    11, 10, 20, 6, 6, 7,
    15, 22, 7, 25, 7, 2,
    7, 6, 7, 11, 1, 21,
    7, 2, 1, 2, 6, 6,
    15
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1267650600228229401496703205376, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6794415866314396, 24297280210767847, 5832890014087662, 5832890014087662, 10913637427705176, 6714245517659862,
    11768597882173550, 10913637427705176, 20743022336721174, 6794415866314396, 6714245517659862, 7139551352398793,
    15921957128440916, 22129468864167973, 7257387842692651, 25337955744687179, 7294620748891626, 2321928094887362,
    7257387842692651, 6442943495848725, 7294620748891626, 11259154768866839, 1584962500720924, 21129469807493823,
    7257387842692651, 2321928094887362, 1584962500720924, 2321928094887362, 6266786540694901, 6442943495848725,
    15921957128440916
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 31
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
noncomputable def positiveFloor : ℝ := 320765563 / 1000000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 389430386467561716554800300032, coefficient := 389430386467561716554800300032 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 16575308015480174174973984768, coefficient := 16575308015480174174973984768 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 586376246177923846184632320, coefficient := 586376246177923846184632320 }, { argument := 43333483212171061542111936512, coefficient := 43333483212171061542111936512 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 400566283873413318586830684160, coefficient := 400566283873413318586830684160 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 43333511546369958759983218688, coefficient := 43333511546369958759983218688 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 586376246177923846184632320, coefficient := 586376246177923846184632320 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2
