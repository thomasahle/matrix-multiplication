import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

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
def constantNumerator : ℤ := (-28150409732270257242941301679194112)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    495687971111595, 13990361755532097, 90380468101, 274119968086791037, 3521316939, 5868861565,
    179587163889, 5868861565, 3521316939, 2876915939163, 184282253141, 13990375889918379,
    179587163889, 5868861565, 184282253141, 5868861565, 179587163889, 5868861565,
    495687971111595, 7263, 21789, 45999, 118629, 99261,
    2776887, 84735, 99261, 89577, 45999, 45999,
    89577, 2776887, 89577, 7263, 118629, 96540765,
    45641994435, 1732533716265, 182568102955, 96540765, 724746810542379, 4095258615,
    13997081550917071, 46217918655, 4095258615, 13997083516792531, 4095258615, 4095258615,
    169777721439, 1053066501, 46217918655, 169777721439, 724753029619089, 4095258615,
    1053066501, 4095258615, 8554245, 4044227355, 153515645745, 16176920515,
    8554245, 18371038455, 718949856009, 718949856009
  ]
def negativeCoefficients : Array ℕ := #[
    279047520248777053490003312640, 31503493994496395152352719405056, 3334450728642433845137802002432, 308631646532621092389106732761088, 2078618636036841877488499949568, 108261387293585514452526039040,
    3312798451183716742247296794624, 3464364393394736462480833249280, 2078618636036841877488499949568, 53069732051315619184628264337408, 3399407561018585153809317625856, 31503525822304791515277916372992,
    3312798451183716742247296794624, 108261387293585514452526039040, 3399407561018585153809317625856, 108261387293585514452526039040, 3312798451183716742247296794624, 3464364393394736462480833249280,
    279047520248777053490003312640, 548776764241315730993184768, 411582573180986798244888576, 434448271691041620369604608, 560209613496343142055542784, 7499949111297981656906858496,
    13113478095516440488524644352, 400149723925959387182530560, 7499949111297981656906858496, 423015422436014209307246592, 434448271691041620369604608, 434448271691041620369604608,
    423015422436014209307246592, 13113478095516440488524644352, 423015422436014209307246592, 548776764241315730993184768, 560209613496343142055542784, 1780862784635136500815626240,
    210486547589030146165954314240, 1997475378938335909093457264640, 210486691952096345512298414080, 1780862784635136500815626240, 815992366474153381602835562496, 18886046896639809065802792960,
    31518625628492282594910544068608, 213142529262077845171202949120, 18886046896639809065802792960, 31518630055250277151311751282688, 18886046896639809065802792960, 18886046896639809065802792960,
    782961544200696084413710073856, 19425648236543803610540015616, 213142529262077845171202949120, 782961544200696084413710073856, 815999368532041817735389249536, 18886046896639809065802792960,
    19425648236543803610540015616, 18886046896639809065802792960, 157797968258809563363409920, 18650706748395076242552913920, 176991489273017105869040517120, 18650719540059169855520112640,
    157797968258809563363409920, 84721461186915381809585848320, 3315570998907089054202788315136, 3315570998907089054202788315136
  ]
def negativeScales : Array ℕ := #[
    48, 53, 36, 57, 31, 32,
    37, 32, 31, 41, 37, 53,
    37, 32, 37, 32, 37, 32,
    48, 12, 14, 15, 16, 16,
    21, 16, 16, 16, 15, 15,
    16, 21, 16, 12, 16, 26,
    35, 40, 37, 26, 49, 31,
    53, 35, 31, 53, 31, 31,
    37, 29, 35, 37, 49, 31,
    29, 31, 23, 31, 37, 33,
    23, 34, 39, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    48816425578592553, 53635282785658907, 36395291977947632, 57927585044340989, 31713467938072935, 32450433532140135,
    37385893279945381, 32450433532140135, 31713467938072935, 41387660206119569, 37423126186144369, 53635284243205113,
    37385893279945381, 32450433532140135, 37423126186144369, 32450433532140135, 37385893279945381, 32450433532140135,
    48816425578592553, 12826349865815290, 14411312365441260, 15489314877442711, 16856097210059176, 16598939368622512,
    21405037040014770, 16370670380943905, 16598939368622512, 16450840729627935, 15489314877442711, 15489314877442711,
    16450840729627935, 21405037040014770, 16450840729627935, 12826349865815290, 16856097210059176, 26524634923119512,
    35409642783852910, 40656020567119349, 37409643773330911, 26524634923119512, 49364470407727591, 31931307422292202,
    53635975568887553, 35427733240835816, 31931307422292202, 53635975771512548, 31931307422292202, 31931307422292202,
    37304856201838076, 29971949414243735, 35427733240835816, 37304856201838076, 49364482787489050, 31931307422292202,
    29971949414243735, 31931307422292202, 23028209096999409, 31913216963258337, 37159594740975035, 33913217952736435,
    23028209096999409, 34096714128482083, 39387100195496644, 39387100195496644
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
noncomputable def negativeCeiling : ℝ := 8577991981 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 279047520248777053490003312640, coefficient := (-279047520248777053490003312640) }, { argument := 31503493994496395152352719405056, coefficient := (-31503493994496395152352719405056) }, { argument := 3334450728642433845137802002432, coefficient := (-3334450728642433845137802002432) }, { argument := 308631646532621092389106732761088, coefficient := (-308631646532621092389106732761088) }, { argument := 2078618636036841877488499949568, coefficient := (-2078618636036841877488499949568) }, { argument := 108261387293585514452526039040, coefficient := (-108261387293585514452526039040) }, { argument := 3312798451183716742247296794624, coefficient := (-3312798451183716742247296794624) }, { argument := 3464364393394736462480833249280, coefficient := (-3464364393394736462480833249280) }, { argument := 2078618636036841877488499949568, coefficient := (-2078618636036841877488499949568) }, { argument := 53069732051315619184628264337408, coefficient := (-53069732051315619184628264337408) }, { argument := 3399407561018585153809317625856, coefficient := (-3399407561018585153809317625856) }, { argument := 31503525822304791515277916372992, coefficient := (-31503525822304791515277916372992) }, { argument := 3312798451183716742247296794624, coefficient := (-3312798451183716742247296794624) }, { argument := 108261387293585514452526039040, coefficient := (-108261387293585514452526039040) }, { argument := 3399407561018585153809317625856, coefficient := (-3399407561018585153809317625856) }, { argument := 108261387293585514452526039040, coefficient := (-108261387293585514452526039040) }, { argument := 3312798451183716742247296794624, coefficient := (-3312798451183716742247296794624) }, { argument := 3464364393394736462480833249280, coefficient := (-3464364393394736462480833249280) }, { argument := 279047520248777053490003312640, coefficient := (-279047520248777053490003312640) }, { argument := 548776764241315730993184768, coefficient := (-548776764241315730993184768) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 560209613496343142055542784, coefficient := (-560209613496343142055542784) }, { argument := 7499949111297981656906858496, coefficient := (-7499949111297981656906858496) }, { argument := 13113478095516440488524644352, coefficient := (-13113478095516440488524644352) }, { argument := 400149723925959387182530560, coefficient := (-400149723925959387182530560) }, { argument := 7499949111297981656906858496, coefficient := (-7499949111297981656906858496) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 13113478095516440488524644352, coefficient := (-13113478095516440488524644352) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 548776764241315730993184768, coefficient := (-548776764241315730993184768) }, { argument := 560209613496343142055542784, coefficient := (-560209613496343142055542784) }, { argument := 1780862784635136500815626240, coefficient := (-1780862784635136500815626240) }, { argument := 210486547589030146165954314240, coefficient := (-210486547589030146165954314240) }, { argument := 1997475378938335909093457264640, coefficient := (-1997475378938335909093457264640) }, { argument := 210486691952096345512298414080, coefficient := (-210486691952096345512298414080) }, { argument := 1780862784635136500815626240, coefficient := (-1780862784635136500815626240) }, { argument := 815992366474153381602835562496, coefficient := (-815992366474153381602835562496) }, { argument := 18886046896639809065802792960, coefficient := (-18886046896639809065802792960) }, { argument := 31518625628492282594910544068608, coefficient := (-31518625628492282594910544068608) }, { argument := 213142529262077845171202949120, coefficient := (-213142529262077845171202949120) }, { argument := 18886046896639809065802792960, coefficient := (-18886046896639809065802792960) }, { argument := 31518630055250277151311751282688, coefficient := (-31518630055250277151311751282688) }, { argument := 18886046896639809065802792960, coefficient := (-18886046896639809065802792960) }, { argument := 18886046896639809065802792960, coefficient := (-18886046896639809065802792960) }, { argument := 782961544200696084413710073856, coefficient := (-782961544200696084413710073856) }, { argument := 19425648236543803610540015616, coefficient := (-19425648236543803610540015616) }, { argument := 213142529262077845171202949120, coefficient := (-213142529262077845171202949120) }, { argument := 782961544200696084413710073856, coefficient := (-782961544200696084413710073856) }, { argument := 815999368532041817735389249536, coefficient := (-815999368532041817735389249536) }, { argument := 18886046896639809065802792960, coefficient := (-18886046896639809065802792960) }, { argument := 19425648236543803610540015616, coefficient := (-19425648236543803610540015616) }, { argument := 18886046896639809065802792960, coefficient := (-18886046896639809065802792960) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 18650706748395076242552913920, coefficient := (-18650706748395076242552913920) }, { argument := 176991489273017105869040517120, coefficient := (-176991489273017105869040517120) }, { argument := 18650719540059169855520112640, coefficient := (-18650719540059169855520112640) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 84721461186915381809585848320, coefficient := (-84721461186915381809585848320) }, { argument := 3315570998907089054202788315136, coefficient := (-3315570998907089054202788315136) }, { argument := 3315570998907089054202788315136, coefficient := (-3315570998907089054202788315136) }] }

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
def constantNumerator : ℤ := (-58837337092373621490232837346951168)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    18371038455, 437690349979615, 4509, 117, 1615463709652271, 7263,
    218822003761529, 7263, 7569, 4509, 225, 108518703977427,
    4658224317967405, 2040098099, 165413181, 35453554661, 64124790301, 291139005136575,
    35453554661, 1047608213, 1047613013, 2040098099, 2040088499, 64124790301,
    2040088499, 6782414074177, 165413181, 123922008152037, 13990363712260257, 90380468101,
    137060003799109127, 3521316939, 5868861565, 179587163889, 5868861565, 3521316939,
    2876915939163, 184282253141, 6995188923321543, 179587163889, 5868861565, 184282253141,
    5868861565, 179587163889, 5868861565, 123922008152037, 7093970279200815, 155452751685,
    274349635132096043, 1754395340445, 155452751685, 137174837416613533, 155452751685, 155452751685,
    6444626934141, 39973564719, 1754395340445, 6444626934141, 1773508576750875, 155452751685,
    39973564719, 155452751685, 8554245, 4044227355
  ]
def negativeCoefficients : Array ℕ := #[
    84721461186915381809585848320, 123198881066991005969353277440, 340690407540147684296884224, 17680540111863951680077824, 454712610051282926117140299776, 548776764241315730993184768,
    123185836825110909806914306048, 548776764241315730993184768, 571897470541445513959440384, 340690407540147684296884224, 17000519338330722769305600, 122181198698867349842137448448,
    5244694325651547008266896670720, 75266335035028744259887955968, 97642707722406252892360015872, 1308005298669478802511313764352, 2365787190925678969113471352832, 5244694060184384363618421964800,
    1308005298669478802511313764352, 77299842378908814597876088832, 77300196556395029821267116032, 75266335035028744259887955968, 75265980857542529036496928768, 2365787190925678969113471352832,
    75265980857542529036496928768, 122181109988543779267221127168, 97642707722406252892360015872, 279047554868258700411248050176, 31503498400656501273030857588736, 3334450728642433845137802002432,
    308631691018533315228525182058496, 2078618636036841877488499949568, 108261387293585514452526039040, 3312798451183716742247296794624, 3464364393394736462480833249280, 2078618636036841877488499949568,
    53069732051315619184628264337408, 3399407561018585153809317625856, 31503530228457122171199399395328, 3312798451183716742247296794624, 108261387293585514452526039040, 3399407561018585153809317625856,
    108261387293585514452526039040, 3312798451183716742247296794624, 3464364393394736462480833249280, 279047554868258700411248050176, 7987100476496540976164697538560, 179224820367944766510921154560,
    308890228637534819350219254136832, 2022680115581090936337538744320, 179224820367944766510921154560, 308890273337034539692728919261184, 179224820367944766510921154560, 179224820367944766510921154560,
    7430148981539653034495617007616, 184345529521314616982661758976, 2022680115581090936337538744320, 7430148981539653034495617007616, 7987172565393619355575517184000, 179224820367944766510921154560,
    184345529521314616982661758976, 179224820367944766510921154560, 157797968258809563363409920, 18650706748395076242552913920
  ]
def negativeScales : Array ℕ := #[
    34, 48, 12, 6, 50, 12,
    47, 12, 12, 12, 7, 46,
    52, 30, 27, 35, 35, 48,
    35, 29, 29, 30, 30, 35,
    30, 42, 27, 46, 53, 36,
    56, 31, 32, 37, 32, 31,
    41, 37, 52, 37, 32, 37,
    32, 37, 32, 46, 52, 37,
    57, 40, 37, 56, 37, 37,
    42, 35, 40, 42, 50, 37,
    35, 37, 23, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34096714128482083, 48636903904807236, 12138591794637521, 6870364722125690, 50520869765066977, 12826349865815290,
    47636751144820670, 12826349865815290, 12885886995081222, 12138591794637521, 7813781192070436, 46624937051379428,
    52048701537875740, 30925991387375993, 27301498959784988, 35045211231760152, 35900163156122618, 48048701464851814,
    35045211231760152, 29964452142496775, 29964458752717822, 30925991387375993, 30925984598532531, 35900163156122618,
    30925984598532531, 42624936003902470, 27301498959784988, 46816425757577668, 53635282987437950, 36395291977947632,
    56927585252289879, 31713467938072935, 32450433532140135, 37385893279945381, 32450433532140135, 31713467938072935,
    41387660206119569, 37423126186144369, 52635284444983597, 37385893279945381, 32450433532140135, 37423126186144369,
    32450433532140135, 37385893279945381, 32450433532140135, 46816425757577668, 52655514709325628, 37177685197957931,
    57928793277453456, 40674111024116320, 37177685197957931, 56928793486225842, 37177685197957931, 37177685197957931,
    42551233985081089, 35218327182455277, 40674111024116320, 42551233985081089, 50655527730549706, 37177685197957931,
    35218327182455277, 37177685197957931, 23028209096999409, 31913216963258337
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
noncomputable def negativeCeiling : ℝ := 749464930093 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 84721461186915381809585848320, coefficient := (-84721461186915381809585848320) }, { argument := 123198881066991005969353277440, coefficient := (-123198881066991005969353277440) }, { argument := 340690407540147684296884224, coefficient := (-340690407540147684296884224) }, { argument := 17680540111863951680077824, coefficient := (-17680540111863951680077824) }, { argument := 454712610051282926117140299776, coefficient := (-454712610051282926117140299776) }, { argument := 548776764241315730993184768, coefficient := (-548776764241315730993184768) }, { argument := 123185836825110909806914306048, coefficient := (-123185836825110909806914306048) }, { argument := 548776764241315730993184768, coefficient := (-548776764241315730993184768) }, { argument := 571897470541445513959440384, coefficient := (-571897470541445513959440384) }, { argument := 340690407540147684296884224, coefficient := (-340690407540147684296884224) }, { argument := 17000519338330722769305600, coefficient := (-17000519338330722769305600) }, { argument := 122181198698867349842137448448, coefficient := (-122181198698867349842137448448) }, { argument := 5244694325651547008266896670720, coefficient := (-5244694325651547008266896670720) }, { argument := 75266335035028744259887955968, coefficient := (-75266335035028744259887955968) }, { argument := 97642707722406252892360015872, coefficient := (-97642707722406252892360015872) }, { argument := 1308005298669478802511313764352, coefficient := (-1308005298669478802511313764352) }, { argument := 2365787190925678969113471352832, coefficient := (-2365787190925678969113471352832) }, { argument := 5244694060184384363618421964800, coefficient := (-5244694060184384363618421964800) }, { argument := 1308005298669478802511313764352, coefficient := (-1308005298669478802511313764352) }, { argument := 77299842378908814597876088832, coefficient := (-77299842378908814597876088832) }, { argument := 77300196556395029821267116032, coefficient := (-77300196556395029821267116032) }, { argument := 75266335035028744259887955968, coefficient := (-75266335035028744259887955968) }, { argument := 75265980857542529036496928768, coefficient := (-75265980857542529036496928768) }, { argument := 2365787190925678969113471352832, coefficient := (-2365787190925678969113471352832) }, { argument := 75265980857542529036496928768, coefficient := (-75265980857542529036496928768) }, { argument := 122181109988543779267221127168, coefficient := (-122181109988543779267221127168) }, { argument := 97642707722406252892360015872, coefficient := (-97642707722406252892360015872) }, { argument := 279047554868258700411248050176, coefficient := (-279047554868258700411248050176) }, { argument := 31503498400656501273030857588736, coefficient := (-31503498400656501273030857588736) }, { argument := 3334450728642433845137802002432, coefficient := (-3334450728642433845137802002432) }, { argument := 308631691018533315228525182058496, coefficient := (-308631691018533315228525182058496) }, { argument := 2078618636036841877488499949568, coefficient := (-2078618636036841877488499949568) }, { argument := 108261387293585514452526039040, coefficient := (-108261387293585514452526039040) }, { argument := 3312798451183716742247296794624, coefficient := (-3312798451183716742247296794624) }, { argument := 3464364393394736462480833249280, coefficient := (-3464364393394736462480833249280) }, { argument := 2078618636036841877488499949568, coefficient := (-2078618636036841877488499949568) }, { argument := 53069732051315619184628264337408, coefficient := (-53069732051315619184628264337408) }, { argument := 3399407561018585153809317625856, coefficient := (-3399407561018585153809317625856) }, { argument := 31503530228457122171199399395328, coefficient := (-31503530228457122171199399395328) }, { argument := 3312798451183716742247296794624, coefficient := (-3312798451183716742247296794624) }, { argument := 108261387293585514452526039040, coefficient := (-108261387293585514452526039040) }, { argument := 3399407561018585153809317625856, coefficient := (-3399407561018585153809317625856) }, { argument := 108261387293585514452526039040, coefficient := (-108261387293585514452526039040) }, { argument := 3312798451183716742247296794624, coefficient := (-3312798451183716742247296794624) }, { argument := 3464364393394736462480833249280, coefficient := (-3464364393394736462480833249280) }, { argument := 279047554868258700411248050176, coefficient := (-279047554868258700411248050176) }, { argument := 7987100476496540976164697538560, coefficient := (-7987100476496540976164697538560) }, { argument := 179224820367944766510921154560, coefficient := (-179224820367944766510921154560) }, { argument := 308890228637534819350219254136832, coefficient := (-308890228637534819350219254136832) }, { argument := 2022680115581090936337538744320, coefficient := (-2022680115581090936337538744320) }, { argument := 179224820367944766510921154560, coefficient := (-179224820367944766510921154560) }, { argument := 308890273337034539692728919261184, coefficient := (-308890273337034539692728919261184) }, { argument := 179224820367944766510921154560, coefficient := (-179224820367944766510921154560) }, { argument := 179224820367944766510921154560, coefficient := (-179224820367944766510921154560) }, { argument := 7430148981539653034495617007616, coefficient := (-7430148981539653034495617007616) }, { argument := 184345529521314616982661758976, coefficient := (-184345529521314616982661758976) }, { argument := 2022680115581090936337538744320, coefficient := (-2022680115581090936337538744320) }, { argument := 7430148981539653034495617007616, coefficient := (-7430148981539653034495617007616) }, { argument := 7987172565393619355575517184000, coefficient := (-7987172565393619355575517184000) }, { argument := 179224820367944766510921154560, coefficient := (-179224820367944766510921154560) }, { argument := 184345529521314616982661758976, coefficient := (-184345529521314616982661758976) }, { argument := 179224820367944766510921154560, coefficient := (-179224820367944766510921154560) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 18650706748395076242552913920, coefficient := (-18650706748395076242552913920) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
