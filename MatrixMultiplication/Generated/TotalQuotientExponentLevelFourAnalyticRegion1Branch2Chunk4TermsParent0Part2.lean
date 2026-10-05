import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1558787135047703329648037867814912)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    456601059, 38395236893, 19197613815, 228305161, 59799, 715659,
    1070595, 310569, 59799, 1240347, 623067, 59799,
    715659, 59799, 7128211437, 599405895699, 299702875545, 3564178023,
    19880151, 1468097133, 15301730895, 1468097133, 19880151, 8724861,
    733666947, 366833385, 4362519, 5411895, 399654285, 4165529775,
    399654285, 5411895, 577512711, 52311, 19959051513, 1294419,
    41181, 159672470721, 21147, 21147, 715659, 38955,
    1294419, 715659, 4620043071, 41181, 38955, 52311,
    3485252512117, 9352937895, 22412257355915, 14740401165, 463159219, 14739811341,
    9972524297, 3503474578805, 9352937895, 55670529, 38010121881945, 1651796139591335,
    4520983705, 4004299853, 187427067313, 51022530385
  ]
def negativeCoefficients : Array ℕ := #[
    2105700719789438831570190336, 177066777153655521893282742272, 177066734435607933200388587520, 2105743437837027524464345088, 282392793309121914133807104, 6759208149528014847976931328,
    5055741944727827817556869120, 5866482544873371377489412096, 282392793309121914133807104, 5857373099927915831872192512, 5884701434764282468723851264, 282392793309121914133807104,
    6759208149528014847976931328, 282392793309121914133807104, 32873073020407099211328258048, 2764271788558023465990038224896, 2764271121666720027223900815360, 32873739911710537977465667584,
    5867584922299216260293984256, 866611586809527468869283741696, 9032547638554867303012620042240, 866611586809527468869283741696, 5867584922299216260293984256, 1287562223565516737775403008,
    108270131253190637590797090816, 108270105132601029218072002560, 1287588344155125110500491264, 1597309472300613661485957120, 235914250027404100760418385920, 2458894774106941822667115724800,
    235914250027404100760418385920, 1597309472300613661485957120, 10653229179131186980350590976, 494063426170788021547302912, 368179515214296409703876395008, 12225441800779286575734325248,
    388943548262109719090429952, 368179650375896080782974779392, 399455536052977549336117248, 399455536052977549336117248, 6759208149528014847976931328, 367919572680374058599055360,
    12225441800779286575734325248, 6759208149528014847976931328, 10653094017531515901252206592, 388943548262109719090429952, 367919572680374058599055360, 494063426170788021547302912,
    3924045478715551573772075008, 10783203230397796158296555520, 50467916938315225972521041920, 16994525489660320032007127040, 533986223642012147456671744, 16993845468886786803096354816,
    11497537717225578900720975872, 3944561701902050855820984320, 10783203230397796158296555520, 513470000455512865407762432, 42795592685958659537822023680, 1859757119688890025241519063040,
    20849357341886550439698104320, 18466573645670944675161178112, 864354785802210991085769981952, 235299890001291069248021463040
  ]
def negativeScales : Array ℕ := #[
    28, 35, 34, 27, 15, 19,
    20, 18, 15, 20, 19, 15,
    19, 15, 32, 39, 38, 31,
    24, 30, 33, 30, 24, 23,
    29, 28, 22, 22, 28, 31,
    28, 22, 29, 15, 34, 20,
    15, 37, 14, 14, 19, 15,
    20, 19, 32, 15, 15, 15,
    41, 33, 44, 33, 28, 33,
    33, 41, 33, 25, 45, 50,
    32, 31, 37, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28766358965044524, 35160208297917340, 34160207949861517, 27766388232494610, 15867833740861174, 19448912804669952,
    20029981389286572, 18244554306163721, 15867833740861174, 20242312355377051, 19249027782743029, 15867833740861174,
    19448912804669952, 15867833740861174, 32730892984846791, 39124742317892552, 38124741969836729, 31730922252296773,
    24244825379166255, 30451300277658934, 33832975806462894, 30451300277658934, 24244825379166255, 23056700716553848,
    29450550049746917, 28450549701691094, 22056729984003733, 22367702418163978, 28574177316659328, 31955852855716562,
    28574177316659328, 22367702418163978, 29105277459558077, 15674826729059175, 34216324111933341, 20303873258815179,
    15329691242970910, 37216324641557956, 14368165390785547, 14368165390785547, 19448912804669952, 15249520894286927,
    20303873258815179, 19448912804669952, 32105259155417304, 15329691242970910, 15249520894286927, 15674826729059175,
    41664400324121764, 33122772461851995, 44349353197518907, 33779056737693010, 28786932989740702, 33778999008382734,
    33215311587276761, 41671923566766293, 33122772461851995, 25730410456597251, 45111448884839134, 50552957067364092,
    32073989571740908, 31898902869465304, 37447538358862728, 35570415397862847
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
noncomputable def negativeCeiling : ℝ := 5154468179 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2105700719789438831570190336, coefficient := (-2105700719789438831570190336) }, { argument := 177066777153655521893282742272, coefficient := (-177066777153655521893282742272) }, { argument := 177066734435607933200388587520, coefficient := (-177066734435607933200388587520) }, { argument := 2105743437837027524464345088, coefficient := (-2105743437837027524464345088) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 6759208149528014847976931328, coefficient := (-6759208149528014847976931328) }, { argument := 5055741944727827817556869120, coefficient := (-5055741944727827817556869120) }, { argument := 5866482544873371377489412096, coefficient := (-5866482544873371377489412096) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 5857373099927915831872192512, coefficient := (-5857373099927915831872192512) }, { argument := 5884701434764282468723851264, coefficient := (-5884701434764282468723851264) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 6759208149528014847976931328, coefficient := (-6759208149528014847976931328) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 32873073020407099211328258048, coefficient := (-32873073020407099211328258048) }, { argument := 2764271788558023465990038224896, coefficient := (-2764271788558023465990038224896) }, { argument := 2764271121666720027223900815360, coefficient := (-2764271121666720027223900815360) }, { argument := 32873739911710537977465667584, coefficient := (-32873739911710537977465667584) }, { argument := 5867584922299216260293984256, coefficient := (-5867584922299216260293984256) }, { argument := 866611586809527468869283741696, coefficient := (-866611586809527468869283741696) }, { argument := 9032547638554867303012620042240, coefficient := (-9032547638554867303012620042240) }, { argument := 866611586809527468869283741696, coefficient := (-866611586809527468869283741696) }, { argument := 5867584922299216260293984256, coefficient := (-5867584922299216260293984256) }, { argument := 1287562223565516737775403008, coefficient := (-1287562223565516737775403008) }, { argument := 108270131253190637590797090816, coefficient := (-108270131253190637590797090816) }, { argument := 108270105132601029218072002560, coefficient := (-108270105132601029218072002560) }, { argument := 1287588344155125110500491264, coefficient := (-1287588344155125110500491264) }, { argument := 1597309472300613661485957120, coefficient := (-1597309472300613661485957120) }, { argument := 235914250027404100760418385920, coefficient := (-235914250027404100760418385920) }, { argument := 2458894774106941822667115724800, coefficient := (-2458894774106941822667115724800) }, { argument := 235914250027404100760418385920, coefficient := (-235914250027404100760418385920) }, { argument := 1597309472300613661485957120, coefficient := (-1597309472300613661485957120) }, { argument := 10653229179131186980350590976, coefficient := (-10653229179131186980350590976) }, { argument := 494063426170788021547302912, coefficient := (-494063426170788021547302912) }, { argument := 368179515214296409703876395008, coefficient := (-368179515214296409703876395008) }, { argument := 12225441800779286575734325248, coefficient := (-12225441800779286575734325248) }, { argument := 388943548262109719090429952, coefficient := (-388943548262109719090429952) }, { argument := 368179650375896080782974779392, coefficient := (-368179650375896080782974779392) }, { argument := 399455536052977549336117248, coefficient := (-399455536052977549336117248) }, { argument := 399455536052977549336117248, coefficient := (-399455536052977549336117248) }, { argument := 6759208149528014847976931328, coefficient := (-6759208149528014847976931328) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 12225441800779286575734325248, coefficient := (-12225441800779286575734325248) }, { argument := 6759208149528014847976931328, coefficient := (-6759208149528014847976931328) }, { argument := 10653094017531515901252206592, coefficient := (-10653094017531515901252206592) }, { argument := 388943548262109719090429952, coefficient := (-388943548262109719090429952) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 494063426170788021547302912, coefficient := (-494063426170788021547302912) }, { argument := 3924045478715551573772075008, coefficient := (-3924045478715551573772075008) }, { argument := 10783203230397796158296555520, coefficient := (-10783203230397796158296555520) }, { argument := 50467916938315225972521041920, coefficient := (-50467916938315225972521041920) }, { argument := 16994525489660320032007127040, coefficient := (-16994525489660320032007127040) }, { argument := 533986223642012147456671744, coefficient := (-533986223642012147456671744) }, { argument := 16993845468886786803096354816, coefficient := (-16993845468886786803096354816) }, { argument := 11497537717225578900720975872, coefficient := (-11497537717225578900720975872) }, { argument := 3944561701902050855820984320, coefficient := (-3944561701902050855820984320) }, { argument := 10783203230397796158296555520, coefficient := (-10783203230397796158296555520) }, { argument := 513470000455512865407762432, coefficient := (-513470000455512865407762432) }, { argument := 42795592685958659537822023680, coefficient := (-42795592685958659537822023680) }, { argument := 1859757119688890025241519063040, coefficient := (-1859757119688890025241519063040) }, { argument := 20849357341886550439698104320, coefficient := (-20849357341886550439698104320) }, { argument := 18466573645670944675161178112, coefficient := (-18466573645670944675161178112) }, { argument := 864354785802210991085769981952, coefficient := (-864354785802210991085769981952) }, { argument := 235299890001291069248021463040, coefficient := (-235299890001291069248021463040) }] }

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

end TermShard4


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2539932921218893298066486561079296)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    825898316906631, 187427067313, 4520983705, 4520983705, 1937564445, 4520983705,
    51022530385, 1937564445, 19004813830009, 4004299853, 40929712329093, 3330856856616783,
    19342689165, 32327794601903445, 19848380385, 632114025, 19342689165, 10998784035,
    19848380385, 309862295055, 379268415, 1665429557767209, 19342689165, 632114025,
    379268415, 632114025, 9734555985, 10998784035, 40929712329093, 444967911,
    37417014297, 18708502635, 222488469, 19880151, 1468097133, 15301730895,
    1468097133, 19880151, 90882231075313, 78255, 1597657810764755, 1936395,
    61605, 1597658526800037, 31635, 31635, 1070595, 58275,
    1936395, 1070595, 90881313522975, 61605, 58275, 78255,
    479535, 35412405, 369097575, 35412405, 479535, 909925677,
    22701, 32133947091, 561729, 17871
  ]
def negativeCoefficients : Array ℕ := #[
    1859757676133311594123638079488, 864354785802210991085769981952, 20849357341886550439698104320, 20849357341886550439698104320, 17870877721617043234026946560, 20849357341886550439698104320,
    235299890001291069248021463040, 17870877721617043234026946560, 42795036241537090655703007232, 18466573645670944675161178112, 23041379649210603843423830016, 1875105712285475692836129079296,
    178404818362034852699905720320, 18198930465355285872605229219840, 183068996619865829241079726080, 5830222822288720676467507200, 178404818362034852699905720320, 101445877107823739770534625280,
    183068996619865829241079726080, 2857975227485930875604372029440, 111940278187943436988176138240, 1875106983943053098666390716416, 178404818362034852699905720320, 5830222822288720676467507200,
    111940278187943436988176138240, 5830222822288720676467507200, 179570862926492596835199221760, 101445877107823739770534625280, 23041379649210603843423830016, 2052052293807542300829548544,
    172555521684772578660332863488, 172555480055082890316302254080, 2052093923497230644860157952, 5867584922299216260293984256, 866611586809527468869283741696, 9032547638554867303012620042240,
    866611586809527468869283741696, 5867584922299216260293984256, 51162147750672367349091270656, 369548789116964086197780480, 1798802780306428257750870917120, 9144366845596366643574865920,
    290921387177184493389742080, 1798803586490485557582876377088, 298784127371162452670545920, 298784127371162452670545920, 5055741944727827817556869120, 275195906789228574828134400,
    9144366845596366643574865920, 5055741944727827817556869120, 51161631214626428633166643200, 290921387177184493389742080, 275195906789228574828134400, 369548789116964086197780480,
    141533750710180957346856960, 20903794306225679814214287360, 217876752136058136185693798400, 20903794306225679814214287360, 141533750710180957346856960, 16785166089715901655555244032,
    428809766110495263984451584, 592766698065800535729877549056, 10610760808223531744976961536, 337573645661453718455844864
  ]
def negativeScales : Array ℕ := #[
    49, 37, 32, 32, 30, 32,
    35, 30, 44, 31, 45, 51,
    34, 54, 34, 29, 34, 33,
    34, 38, 28, 50, 34, 29,
    28, 29, 33, 33, 45, 28,
    35, 34, 27, 24, 30, 33,
    30, 24, 46, 16, 50, 20,
    15, 50, 14, 14, 20, 15,
    20, 20, 46, 15, 15, 16,
    18, 25, 28, 25, 18, 29,
    14, 34, 19, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    49552957499022334, 37447538358862728, 32073989571740908, 32073989571740908, 30851597152190147, 32073989571740908,
    35570415397862847, 30851597152190147, 44111430126252648, 31898902869465304, 45218213760496298, 51564814778919947,
    34171069331863587, 54843624610076752, 34208302238062562, 29235609584058297, 34171069331863587, 33356624985019664,
    34208302238062562, 38172836258037775, 28498643989892350, 50564815757325296, 34171069331863587, 29235609584058297,
    28498643989892350, 29235609584058297, 33180468029865836, 33356624985019664, 45218213760496298, 28729126058666865,
    35122975391718365, 34122975043662542, 27729155326116844, 24244825379166255, 30451300277658934, 33832975806462894,
    30451300277658934, 24244825379166255, 46369063485651424, 16255895313636262, 50504879865633571, 20884941846757732,
    15910759832877788, 50504880512217785, 14949233985692235, 14949233985692235, 20029981389286572, 15830589480093830,
    20884941846757732, 20029981389286572, 46369048920044104, 15910759832877788, 15830589480093830, 16255895313636262,
    18871276594630224, 25077751490537107, 28459427018094118, 25077751490537107, 18871276594630224, 29761173469748949,
    14470468230513509, 34903379154953503, 19099514760308992, 14125332744464723
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
noncomputable def negativeCeiling : ℝ := 24990617461 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1859757676133311594123638079488, coefficient := (-1859757676133311594123638079488) }, { argument := 864354785802210991085769981952, coefficient := (-864354785802210991085769981952) }, { argument := 20849357341886550439698104320, coefficient := (-20849357341886550439698104320) }, { argument := 20849357341886550439698104320, coefficient := (-20849357341886550439698104320) }, { argument := 17870877721617043234026946560, coefficient := (-17870877721617043234026946560) }, { argument := 20849357341886550439698104320, coefficient := (-20849357341886550439698104320) }, { argument := 235299890001291069248021463040, coefficient := (-235299890001291069248021463040) }, { argument := 17870877721617043234026946560, coefficient := (-17870877721617043234026946560) }, { argument := 42795036241537090655703007232, coefficient := (-42795036241537090655703007232) }, { argument := 18466573645670944675161178112, coefficient := (-18466573645670944675161178112) }, { argument := 23041379649210603843423830016, coefficient := (-23041379649210603843423830016) }, { argument := 1875105712285475692836129079296, coefficient := (-1875105712285475692836129079296) }, { argument := 178404818362034852699905720320, coefficient := (-178404818362034852699905720320) }, { argument := 18198930465355285872605229219840, coefficient := (-18198930465355285872605229219840) }, { argument := 183068996619865829241079726080, coefficient := (-183068996619865829241079726080) }, { argument := 5830222822288720676467507200, coefficient := (-5830222822288720676467507200) }, { argument := 178404818362034852699905720320, coefficient := (-178404818362034852699905720320) }, { argument := 101445877107823739770534625280, coefficient := (-101445877107823739770534625280) }, { argument := 183068996619865829241079726080, coefficient := (-183068996619865829241079726080) }, { argument := 2857975227485930875604372029440, coefficient := (-2857975227485930875604372029440) }, { argument := 111940278187943436988176138240, coefficient := (-111940278187943436988176138240) }, { argument := 1875106983943053098666390716416, coefficient := (-1875106983943053098666390716416) }, { argument := 178404818362034852699905720320, coefficient := (-178404818362034852699905720320) }, { argument := 5830222822288720676467507200, coefficient := (-5830222822288720676467507200) }, { argument := 111940278187943436988176138240, coefficient := (-111940278187943436988176138240) }, { argument := 5830222822288720676467507200, coefficient := (-5830222822288720676467507200) }, { argument := 179570862926492596835199221760, coefficient := (-179570862926492596835199221760) }, { argument := 101445877107823739770534625280, coefficient := (-101445877107823739770534625280) }, { argument := 23041379649210603843423830016, coefficient := (-23041379649210603843423830016) }, { argument := 2052052293807542300829548544, coefficient := (-2052052293807542300829548544) }, { argument := 172555521684772578660332863488, coefficient := (-172555521684772578660332863488) }, { argument := 172555480055082890316302254080, coefficient := (-172555480055082890316302254080) }, { argument := 2052093923497230644860157952, coefficient := (-2052093923497230644860157952) }, { argument := 5867584922299216260293984256, coefficient := (-5867584922299216260293984256) }, { argument := 866611586809527468869283741696, coefficient := (-866611586809527468869283741696) }, { argument := 9032547638554867303012620042240, coefficient := (-9032547638554867303012620042240) }, { argument := 866611586809527468869283741696, coefficient := (-866611586809527468869283741696) }, { argument := 5867584922299216260293984256, coefficient := (-5867584922299216260293984256) }, { argument := 51162147750672367349091270656, coefficient := (-51162147750672367349091270656) }, { argument := 369548789116964086197780480, coefficient := (-369548789116964086197780480) }, { argument := 1798802780306428257750870917120, coefficient := (-1798802780306428257750870917120) }, { argument := 9144366845596366643574865920, coefficient := (-9144366845596366643574865920) }, { argument := 290921387177184493389742080, coefficient := (-290921387177184493389742080) }, { argument := 1798803586490485557582876377088, coefficient := (-1798803586490485557582876377088) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 5055741944727827817556869120, coefficient := (-5055741944727827817556869120) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 9144366845596366643574865920, coefficient := (-9144366845596366643574865920) }, { argument := 5055741944727827817556869120, coefficient := (-5055741944727827817556869120) }, { argument := 51161631214626428633166643200, coefficient := (-51161631214626428633166643200) }, { argument := 290921387177184493389742080, coefficient := (-290921387177184493389742080) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 369548789116964086197780480, coefficient := (-369548789116964086197780480) }, { argument := 141533750710180957346856960, coefficient := (-141533750710180957346856960) }, { argument := 20903794306225679814214287360, coefficient := (-20903794306225679814214287360) }, { argument := 217876752136058136185693798400, coefficient := (-217876752136058136185693798400) }, { argument := 20903794306225679814214287360, coefficient := (-20903794306225679814214287360) }, { argument := 141533750710180957346856960, coefficient := (-141533750710180957346856960) }, { argument := 16785166089715901655555244032, coefficient := (-16785166089715901655555244032) }, { argument := 428809766110495263984451584, coefficient := (-428809766110495263984451584) }, { argument := 592766698065800535729877549056, coefficient := (-592766698065800535729877549056) }, { argument := 10610760808223531744976961536, coefficient := (-10610760808223531744976961536) }, { argument := 337573645661453718455844864, coefficient := (-337573645661453718455844864) }] }

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

end TermShard5


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
