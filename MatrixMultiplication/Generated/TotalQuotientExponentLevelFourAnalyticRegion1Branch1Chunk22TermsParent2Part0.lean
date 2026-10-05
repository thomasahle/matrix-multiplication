import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 22, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22

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
def constantNumerator : ℤ := (-2442491403267987175447483547385856)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1706485, 943, 403796057, 9867, 437, 12618625,
    437, 851, 16077, 851, 9867, 16077,
    13651935, 851, 851, 943, 143769138360059, 8514438135,
    7054820169, 17149603387805899, 47437583895, 4600574882340821, 189993605241, 189993605241,
    135987740499, 7054820169, 72288635799893, 1475280705, 72288646637227, 1475280705,
    1475280705, 5480300175, 92185635, 4404019725, 4404018675, 13442199,
    3649044915, 3649044045, 943, 143769159856389, 8514436105, 7054818487,
    17149605800832821, 47437572585, 4600575570223147, 189993559943, 189993559943, 135987708077,
    7054818487, 8629222955915909, 5480300175, 8629224171136379, 5480300175, 98904283,
    24536681325, 24536675475, 9867, 437, 2313217568811739, 92185635,
    2313217915606309, 92185635, 395617075, 437
  ]
def negativeCoefficients : Array ℕ := #[
    64469180540158452099952148480, 18240272766345524987966783488, 1906872965491720782279367196672, 190855536994200737069213417472, 16905618661490974379091165184, 1906872696316831258709590016000,
    16905618661490974379091165184, 16460733959872790842799292416, 621948812862220583736038129664, 16460733959872790842799292416, 190855536994200737069213417472, 621948812862220583736038129664,
    64469440270315009930438901760, 16460733959872790842799292416, 16460733959872790842799292416, 18240272766345524987966783488, 1294957275891477989567682838528, 157063661207777857193021276160,
    8133653883974210461781458944, 4827184214179652658848012959744, 218767242396547729661708206080, 1294946707862511558380094488576, 219047713220133047263838601216, 219047713220133047263838601216,
    156783190384192539590890881024, 8133653883974210461781458944, 1302236293006078447396912627712, 54428251204033598546572738560, 1302236488234131903755340218368, 54428251204033598546572738560,
    54428251204033598546572738560, 202187389550661337240672665600, 54416794115756858281159557120, 162479649525287438475539251200, 162479610787124883685480857600, 63478990013663862021899157504,
    8414124707559528063911854080, 8414122701476110047998115840, 18240272766345524987966783488, 1294957469513205545234111397888, 157063623760887387562631495680, 8133651944760239713064845312,
    4827184893386349330983945240576, 218767190238378861247951011840, 1294946901484173248901972754432, 219047660995094731582884282368, 219047660995094731582884282368, 156783153004171517227698225152,
    8133651944760239713064845312, 4857820661094977225505120452608, 202187389550661337240672665600, 4857821345203284208629997109248, 202187389550661337240672665600, 1868249084205816169299938639872,
    226310940410221789305215385600, 226310886453495373704776908800, 190855536994200737069213417472, 16905618661490974379091165184, 1302225722615929056249478381568, 54416794115756858281159557120,
    1302225917843916084513402257408, 54416794115756858281159557120, 1868248815030926645730161459200, 16905618661490974379091165184
  ]
def negativeScales : Array ℕ := #[
    20, 9, 28, 13, 8, 23,
    8, 9, 13, 9, 13, 13,
    23, 9, 9, 9, 47, 32,
    32, 53, 35, 52, 37, 37,
    36, 32, 46, 30, 46, 30,
    30, 32, 26, 32, 32, 23,
    31, 31, 9, 47, 32, 32,
    53, 35, 52, 37, 37, 36,
    32, 52, 32, 52, 32, 26,
    34, 34, 13, 8, 51, 26,
    51, 26, 28, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20702596302606878, 9881113963775888, 28589051582168884, 13268395793556559, 8771489469857739, 23589051378517507,
    8771489469857739, 9733015321840403, 13972710616651972, 9733015321840403, 13268395793556559, 13972710616651972,
    23702602114851606, 9733015321840403, 9733015321840403, 9881113963775888, 47030747346944840, 32987264203352225,
    32715962162342690, 53929024737618498, 35465311480859905, 52030735573193321, 37467159905252280, 37467159905252280,
    36984685658461017, 32715962162342690, 46038834098363947, 30458342339431358, 46038834314649213, 30458342339431358,
    30458342339431358, 32351607770734758, 26458038621711320, 32036173784536126, 32036173440570824, 23680265831159728,
    31764871763028918, 31764871419063614, 9881113963775888, 47030747562656270, 32987263859386816, 32715961818377387,
    53929024940612240, 35465311136894604, 52030735788906437, 37467159561286978, 37467159561286978, 36984685314495612,
    32715961818377387, 52938152085313301, 32351607770734758, 52938152288482542, 32351607770734758, 26559529661730227,
    34514221081341203, 34514220737375902, 13268395793556559, 8771489469857739, 51038822387807711, 26458038621711320,
    51038822604094659, 26458038621711320, 28559529453868594, 8771489469857739
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
noncomputable def negativeCeiling : ℝ := 22928404123 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 64469180540158452099952148480, coefficient := (-64469180540158452099952148480) }, { argument := 18240272766345524987966783488, coefficient := (-18240272766345524987966783488) }, { argument := 1906872965491720782279367196672, coefficient := (-1906872965491720782279367196672) }, { argument := 190855536994200737069213417472, coefficient := (-190855536994200737069213417472) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 1906872696316831258709590016000, coefficient := (-1906872696316831258709590016000) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 621948812862220583736038129664, coefficient := (-621948812862220583736038129664) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 190855536994200737069213417472, coefficient := (-190855536994200737069213417472) }, { argument := 621948812862220583736038129664, coefficient := (-621948812862220583736038129664) }, { argument := 64469440270315009930438901760, coefficient := (-64469440270315009930438901760) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 18240272766345524987966783488, coefficient := (-18240272766345524987966783488) }, { argument := 1294957275891477989567682838528, coefficient := (-1294957275891477989567682838528) }, { argument := 157063661207777857193021276160, coefficient := (-157063661207777857193021276160) }, { argument := 8133653883974210461781458944, coefficient := (-8133653883974210461781458944) }, { argument := 4827184214179652658848012959744, coefficient := (-4827184214179652658848012959744) }, { argument := 218767242396547729661708206080, coefficient := (-218767242396547729661708206080) }, { argument := 1294946707862511558380094488576, coefficient := (-1294946707862511558380094488576) }, { argument := 219047713220133047263838601216, coefficient := (-219047713220133047263838601216) }, { argument := 219047713220133047263838601216, coefficient := (-219047713220133047263838601216) }, { argument := 156783190384192539590890881024, coefficient := (-156783190384192539590890881024) }, { argument := 8133653883974210461781458944, coefficient := (-8133653883974210461781458944) }, { argument := 1302236293006078447396912627712, coefficient := (-1302236293006078447396912627712) }, { argument := 54428251204033598546572738560, coefficient := (-54428251204033598546572738560) }, { argument := 1302236488234131903755340218368, coefficient := (-1302236488234131903755340218368) }, { argument := 54428251204033598546572738560, coefficient := (-54428251204033598546572738560) }, { argument := 54428251204033598546572738560, coefficient := (-54428251204033598546572738560) }, { argument := 202187389550661337240672665600, coefficient := (-202187389550661337240672665600) }, { argument := 54416794115756858281159557120, coefficient := (-54416794115756858281159557120) }, { argument := 162479649525287438475539251200, coefficient := (-162479649525287438475539251200) }, { argument := 162479610787124883685480857600, coefficient := (-162479610787124883685480857600) }, { argument := 63478990013663862021899157504, coefficient := (-63478990013663862021899157504) }, { argument := 8414124707559528063911854080, coefficient := (-8414124707559528063911854080) }, { argument := 8414122701476110047998115840, coefficient := (-8414122701476110047998115840) }, { argument := 18240272766345524987966783488, coefficient := (-18240272766345524987966783488) }, { argument := 1294957469513205545234111397888, coefficient := (-1294957469513205545234111397888) }, { argument := 157063623760887387562631495680, coefficient := (-157063623760887387562631495680) }, { argument := 8133651944760239713064845312, coefficient := (-8133651944760239713064845312) }, { argument := 4827184893386349330983945240576, coefficient := (-4827184893386349330983945240576) }, { argument := 218767190238378861247951011840, coefficient := (-218767190238378861247951011840) }, { argument := 1294946901484173248901972754432, coefficient := (-1294946901484173248901972754432) }, { argument := 219047660995094731582884282368, coefficient := (-219047660995094731582884282368) }, { argument := 219047660995094731582884282368, coefficient := (-219047660995094731582884282368) }, { argument := 156783153004171517227698225152, coefficient := (-156783153004171517227698225152) }, { argument := 8133651944760239713064845312, coefficient := (-8133651944760239713064845312) }, { argument := 4857820661094977225505120452608, coefficient := (-4857820661094977225505120452608) }, { argument := 202187389550661337240672665600, coefficient := (-202187389550661337240672665600) }, { argument := 4857821345203284208629997109248, coefficient := (-4857821345203284208629997109248) }, { argument := 202187389550661337240672665600, coefficient := (-202187389550661337240672665600) }, { argument := 1868249084205816169299938639872, coefficient := (-1868249084205816169299938639872) }, { argument := 226310940410221789305215385600, coefficient := (-226310940410221789305215385600) }, { argument := 226310886453495373704776908800, coefficient := (-226310886453495373704776908800) }, { argument := 190855536994200737069213417472, coefficient := (-190855536994200737069213417472) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 1302225722615929056249478381568, coefficient := (-1302225722615929056249478381568) }, { argument := 54416794115756858281159557120, coefficient := (-54416794115756858281159557120) }, { argument := 1302225917843916084513402257408, coefficient := (-1302225917843916084513402257408) }, { argument := 54416794115756858281159557120, coefficient := (-54416794115756858281159557120) }, { argument := 1868248815030926645730161459200, coefficient := (-1868248815030926645730161459200) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }] }

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
def constantNumerator : ℤ := 5580096790127550368163549040082944
def positiveArguments : Array ℕ := #[
    585, 207, 943, 23, 9867, 437,
    23, 437, 851, 16077, 851, 9867,
    16077, 207, 851, 851, 943, 413,
    2065, 1711, 30739, 11505, 413, 46079,
    46079, 32981, 1711, 915, 1005, 915,
    1005, 17, 63, 216006645, 216006667, 569645137,
    4147111837, 1139271617
  ]
def positiveCoefficients : Array ℕ := #[
    46348475070844637492223210946560, 32031698516509214613014839296, 36480545532691049975933566976, 28472620903563746322679857152, 381711073988401474138426834944, 33811237322981948758182330368,
    28472620903563746322679857152, 33811237322981948758182330368, 32921467919745581685598584832, 1243897625724441167472076259328, 32921467919745581685598584832, 381711073988401474138426834944,
    1243897625724441167472076259328, 32031698516509214613014839296, 32921467919745581685598584832, 32921467919745581685598584832, 36480545532691049975933566976, 31954327264053878345833644032,
    639086545281077566916672880640, 33095553237770088286756274176, 594578732306145379220690305024, 890156259498643753919651512320, 31954327264053878345833644032, 891297485472359963860574142464,
    891297485472359963860574142464, 637945319307361356975750250496, 33095553237770088286756274176, 566357567973061475766349332480, 622064869740903588136809922560, 566357567973061475766349332480,
    622064869740903588136809922560, 1346878762742493739090247155712, 9982748476797306536786537742336, 16321000646801952559212496158720, 16321002309074954529327611379712, 5380146204196974401794504392704,
    19584181939760763393709076119552, 5380058099005503502823752466432
  ]
def positiveScales : Array ℕ := #[
    9, 7, 9, 4, 13, 8,
    4, 8, 9, 13, 9, 13,
    13, 7, 9, 9, 9, 8,
    11, 10, 14, 13, 8, 15,
    15, 15, 10, 9, 9, 9,
    9, 4, 5, 27, 27, 29,
    31, 30
  ]
def negativeArguments : Array ℕ := #[
    1475280705, 5480300175, 92185635, 98272554435, 98272531005, 851,
    98272554435, 98272531005, 16077, 851, 70338486465, 70338469695,
    9867, 16077, 6721125, 3649044915, 3649044045, 851,
    851, 943, 23, 59, 15, 17,
    63, 103
  ]
def negativeCoefficients : Array ℕ := #[
    54428251204033598546572738560, 202187389550661337240672665600, 54416794115756858281159557120, 226601082641516945445350277120, 226601028615615239568500981760, 16460733959872790842799292416,
    226601082641516945445350277120, 226601028615615239568500981760, 621948812862220583736038129664, 16460733959872790842799292416, 162189507293992282335404359680, 162189468625005017821756784640,
    190855536994200737069213417472, 621948812862220583736038129664, 63479230854354488373805056000, 8414124707559528063911854080, 8414122701476110047998115840, 16460733959872790842799292416,
    16460733959872790842799292416, 18240272766345524987966783488, 3644495475656159529303021715456, 4674461588341595918019093069824, 2376844875427930127806318510080, 1346878762742493739090247155712,
    9982748476797306536786537742336, 32642002955876907088540107538432
  ]
def negativeScales : Array ℕ := #[
    30, 32, 26, 36, 36, 9,
    36, 36, 13, 9, 36, 36,
    13, 13, 22, 31, 31, 9,
    9, 9, 4, 5, 3, 4,
    5, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9192292814470766, 7693486957495471, 9881113960483342, 4523561956056975, 13268395793556558, 8771489469478456,
    4523561956056975, 8771489469478456, 9733015321676379, 13972710600493500, 9733015321676379, 13268395793556558,
    13972710600493500, 7693486957495471, 9733015321676379, 9733015321676379, 9881113960483342, 8689997971415898,
    11011926066306807, 10740624044478062, 14907782611330225, 13489973363111439, 8689997971415898, 15491821787503807,
    15491821787503807, 15009347522205031, 10740624044478062, 9837627933086892, 9972979785123183, 9837627933086892,
    9972979785123183, 4087462841250339, 5977279922488012, 27686500453711637, 27686500600648271, 29085488224831012,
    31949459806912642, 30085464599085769
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30458342339431358, 32351607770734758, 26458038621711320, 36516069505733599, 36516069161768297, 9733015321840403,
    36516069505733599, 36516069161768297, 13972710616651972, 9733015321840403, 36033595240434350, 36033594896469048,
    13268395793556559, 13972710616651972, 22680271304766211, 31764871763028918, 31764871419063614, 9733015321840403,
    9733015321840403, 9881113963775888, 4523561956057598, 5882643052550791, 3906890600547867, 4087462841250340,
    5977279939904027, 6686500527235738
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 5963571861 / 200000000000
noncomputable def negativeCeiling : ℝ := 4981417337 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 54428251204033598546572738560, coefficient := (-54428251204033598546572738560) }, { argument := 202187389550661337240672665600, coefficient := (-202187389550661337240672665600) }, { argument := 54416794115756858281159557120, coefficient := (-54416794115756858281159557120) }, { argument := 226601082641516945445350277120, coefficient := (-226601082641516945445350277120) }, { argument := 226601028615615239568500981760, coefficient := (-226601028615615239568500981760) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 226601082641516945445350277120, coefficient := (-226601082641516945445350277120) }, { argument := 226601028615615239568500981760, coefficient := (-226601028615615239568500981760) }, { argument := 621948812862220583736038129664, coefficient := (-621948812862220583736038129664) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 162189507293992282335404359680, coefficient := (-162189507293992282335404359680) }, { argument := 162189468625005017821756784640, coefficient := (-162189468625005017821756784640) }, { argument := 190855536994200737069213417472, coefficient := (-190855536994200737069213417472) }, { argument := 621948812862220583736038129664, coefficient := (-621948812862220583736038129664) }, { argument := 63479230854354488373805056000, coefficient := (-63479230854354488373805056000) }, { argument := 8414124707559528063911854080, coefficient := (-8414124707559528063911854080) }, { argument := 8414122701476110047998115840, coefficient := (-8414122701476110047998115840) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 18240272766345524987966783488, coefficient := (-18240272766345524987966783488) }, { argument := 46348475070844637492223210946560, coefficient := 46348475070844637492223210946560 }, { argument := 32031698516509214613014839296, coefficient := 32031698516509214613014839296 }, { argument := 36480545532691049975933566976, coefficient := 36480545532691049975933566976 }, { argument := 28472620903563746322679857152, coefficient := 28472620903563746322679857152 }, { argument := 381711073988401474138426834944, coefficient := 381711073988401474138426834944 }, { argument := 33811237322981948758182330368, coefficient := 33811237322981948758182330368 }, { argument := 28472620903563746322679857152, coefficient := 28472620903563746322679857152 }, { argument := 33811237322981948758182330368, coefficient := 33811237322981948758182330368 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 1243897625724441167472076259328, coefficient := 1243897625724441167472076259328 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 381711073988401474138426834944, coefficient := 381711073988401474138426834944 }, { argument := 1243897625724441167472076259328, coefficient := 1243897625724441167472076259328 }, { argument := 32031698516509214613014839296, coefficient := 32031698516509214613014839296 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 36480545532691049975933566976, coefficient := 36480545532691049975933566976 }, { argument := 3644495475656159529303021715456, coefficient := (-3644495475656159529303021715456) }, { argument := 31954327264053878345833644032, coefficient := 31954327264053878345833644032 }, { argument := 639086545281077566916672880640, coefficient := 639086545281077566916672880640 }, { argument := 33095553237770088286756274176, coefficient := 33095553237770088286756274176 }, { argument := 594578732306145379220690305024, coefficient := 594578732306145379220690305024 }, { argument := 890156259498643753919651512320, coefficient := 890156259498643753919651512320 }, { argument := 31954327264053878345833644032, coefficient := 31954327264053878345833644032 }, { argument := 891297485472359963860574142464, coefficient := 891297485472359963860574142464 }, { argument := 891297485472359963860574142464, coefficient := 891297485472359963860574142464 }, { argument := 637945319307361356975750250496, coefficient := 637945319307361356975750250496 }, { argument := 33095553237770088286756274176, coefficient := 33095553237770088286756274176 }, { argument := 4674461588341595918019093069824, coefficient := (-4674461588341595918019093069824) }, { argument := 566357567973061475766349332480, coefficient := 566357567973061475766349332480 }, { argument := 622064869740903588136809922560, coefficient := 622064869740903588136809922560 }, { argument := 566357567973061475766349332480, coefficient := 566357567973061475766349332480 }, { argument := 622064869740903588136809922560, coefficient := 622064869740903588136809922560 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }, { argument := 9982748476797306536786537742336, coefficient := 9982748476797306536786537742336 }, { argument := 9982748476797306536786537742336, coefficient := (-9982748476797306536786537742336) }, { argument := 16321000646801952559212496158720, coefficient := 16321000646801952559212496158720 }, { argument := 16321002309074954529327611379712, coefficient := 16321002309074954529327611379712 }, { argument := 32642002955876907088540107538432, coefficient := (-32642002955876907088540107538432) }, { argument := 5380146204196974401794504392704, coefficient := 5380146204196974401794504392704 }, { argument := 19584181939760763393709076119552, coefficient := 19584181939760763393709076119552 }, { argument := 5380058099005503502823752466432, coefficient := 5380058099005503502823752466432 }] }

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

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3097504241657678542557194282336256)
def positiveArguments : Array ℕ := #[
    20311103, 793383877, 793383763, 20311209
  ]
def positiveCoefficients : Array ℕ := #[
    95916472037313099508836466688, 3746649428793973205256625979392, 3746648890444194158117071618048, 95916972608160283691229118464
  ]
def positiveScales : Array ℕ := #[
    24, 29, 29, 24
  ]
def negativeArguments : Array ℕ := #[
    383, 97
  ]
def negativeCoefficients : Array ℕ := #[
    30344386242963241298327332978688, 7685131763883640746573763182592
  ]
def negativeScales : Array ℕ := #[
    8, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    24275765251921501, 29563443838698818, 29563443631400369, 24275772781068259
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8581200581928289, 6599912842192769
  ]

abbrev PositiveTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 136129909 / 50000000000
noncomputable def negativeCeiling : ℝ := 149795203 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 30344386242963241298327332978688, coefficient := (-30344386242963241298327332978688) }, { argument := 95916472037313099508836466688, coefficient := 95916472037313099508836466688 }, { argument := 3746649428793973205256625979392, coefficient := 3746649428793973205256625979392 }, { argument := 3746648890444194158117071618048, coefficient := 3746648890444194158117071618048 }, { argument := 95916972608160283691229118464, coefficient := 95916972608160283691229118464 }, { argument := 7685131763883640746573763182592, coefficient := (-7685131763883640746573763182592) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22
