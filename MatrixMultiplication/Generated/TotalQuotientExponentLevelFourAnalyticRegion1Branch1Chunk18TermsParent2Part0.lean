import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 18, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

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
def constantNumerator : ℤ := (-54327269103113242944990546493440)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    163507169, 487602521, 3067932903, 205818907, 20127401, 205818907,
    410988543, 2555007, 487602521, 20127401, 12439805, 562256555,
    1563275, 143957589, 67481127, 219122915, 565106465, 472844185,
    13228104395, 4307259811, 472844185, 426713045, 219122915, 219122915,
    426713045, 13228104395, 426713045, 4498671, 565106465, 10307267,
    465869717, 1295285, 25347881, 4445780183, 1111445179, 6336837,
    2597499, 691463007, 17115429, 23307579189, 5416275, 649953,
    17115429, 34014207, 5416275, 524945373, 33580905, 2765853711,
    17115429, 649953, 33580905, 649953, 17115429, 17115429,
    2597499, 158604863, 56991268425, 3221837063, 24056234475, 2352502425,
    24056234475, 48036581775, 2538666145, 56991268425
  ]
def negativeCoefficients : Array ℕ := #[
    754043725189944028247883776, 17989357829165174379482447872, 14148343274238447667025805312, 15186754811838509396260814848, 742570030231851405810860032, 15186754811838509396260814848,
    15162800939895546447686270976, 754104963768582725531860992, 17989357829165174379482447872, 742570030231851405810860032, 229473899161852448740474880, 10371802773850598562206842880,
    230698670734626394420019200, 2655548801751265336910413824, 19916913273191865819397619712, 2021052166845105906720440320, 2606093583563426037613199360, 34889742669747091442331811840,
    61003864088719380921272238080, 19863729848122893340606726144, 34889742669747091442331811840, 1967866583507076803912007680, 2021052166845105906720440320, 2021052166845105906720440320,
    1967866583507076803912007680, 61003864088719380921272238080, 1967866583507076803912007680, 2655546643482208712892874752, 2606093583563426037613199360, 11883469778024501809774592,
    537111215074405996971425792, 11946895448757438282465280, 116896468404461235731431424, 20502542310942653968057106432, 20502544768971301789854859264, 116894010375813413933678592,
    95830798569432973226016768, 6377620563283318102510534656, 1262895753898986389221933056, 53743618534650228409450364928, 799301110062649613431603200, 47958066603758976805896192,
    1262895753898986389221933056, 1254902742798359893087617024, 799301110062649613431603200, 19367065896818000133447745536, 1238916720597106900818984960, 6377624444017102609157455872,
    1262895753898986389221933056, 47958066603758976805896192, 1238916720597106900818984960, 47958066603758976805896192, 1262895753898986389221933056, 1262895753898986389221933056,
    95830798569432973226016768, 2925743316606765335847108608, 65706458942003690102115532800, 59432403748353037293540343808, 55469900092184207090201395200, 2712250635422256182643916800,
    55469900092184207090201395200, 55382408136202843987535462400, 2926882791587863953166827520, 65706458942003690102115532800
  ]
def negativeScales : Array ℕ := #[
    27, 28, 31, 27, 24, 27,
    28, 21, 28, 24, 23, 29,
    20, 27, 26, 27, 29, 28,
    33, 32, 28, 28, 27, 27,
    28, 33, 28, 22, 29, 23,
    28, 20, 24, 32, 30, 22,
    21, 29, 24, 34, 22, 19,
    24, 25, 22, 28, 25, 31,
    24, 19, 25, 19, 24, 24,
    21, 27, 35, 31, 34, 31,
    34, 35, 31, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27284778651421685, 28861130346229564, 31514619784817219, 27616800276724727, 24262657556963254, 27616800276724727,
    28614522936013129, 21284895813070810, 28861130346229564, 24262657556963254, 23568460534912428, 29066653334685570,
    20576140158437689, 27101068604437007, 26007980732438880, 27707165122691976, 29073947453278000, 28816789614687127,
    33622887285189139, 32004123202580278, 28816789614687127, 28668690974825779, 27707165122691976, 27707165122691976,
    28668690974825779, 33622887285189139, 28668690974825779, 22101067431901474, 29073947453278000, 23297158513092729,
    28795351313455617, 20304838136617414, 24595361811896065, 32049789471551406, 30049789644514615, 22595331475453283,
    21308691763036792, 29365076828919719, 24028794118313064, 34440080117502173, 22368869559910687, 19309975870857117,
    24028794118313064, 25019634119027588, 22368869559910687, 28967592073574580, 25001137775410198, 31365077706788452,
    24028794118313064, 19309975870857117, 25001137775410198, 19309975870857117, 24028794118313064, 24028794118313064,
    21308691763036792, 27240861765439821, 35730021851367526, 31585236388895500, 34485691783848424, 31131549064095726,
    34485691783848424, 35483414443137346, 31241423535453770, 35730021851367526
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
noncomputable def negativeCeiling : ℝ := 16868911 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 754043725189944028247883776, coefficient := (-754043725189944028247883776) }, { argument := 17989357829165174379482447872, coefficient := (-17989357829165174379482447872) }, { argument := 14148343274238447667025805312, coefficient := (-14148343274238447667025805312) }, { argument := 15186754811838509396260814848, coefficient := (-15186754811838509396260814848) }, { argument := 742570030231851405810860032, coefficient := (-742570030231851405810860032) }, { argument := 15186754811838509396260814848, coefficient := (-15186754811838509396260814848) }, { argument := 15162800939895546447686270976, coefficient := (-15162800939895546447686270976) }, { argument := 754104963768582725531860992, coefficient := (-754104963768582725531860992) }, { argument := 17989357829165174379482447872, coefficient := (-17989357829165174379482447872) }, { argument := 742570030231851405810860032, coefficient := (-742570030231851405810860032) }, { argument := 229473899161852448740474880, coefficient := (-229473899161852448740474880) }, { argument := 10371802773850598562206842880, coefficient := (-10371802773850598562206842880) }, { argument := 230698670734626394420019200, coefficient := (-230698670734626394420019200) }, { argument := 2655548801751265336910413824, coefficient := (-2655548801751265336910413824) }, { argument := 19916913273191865819397619712, coefficient := (-19916913273191865819397619712) }, { argument := 2021052166845105906720440320, coefficient := (-2021052166845105906720440320) }, { argument := 2606093583563426037613199360, coefficient := (-2606093583563426037613199360) }, { argument := 34889742669747091442331811840, coefficient := (-34889742669747091442331811840) }, { argument := 61003864088719380921272238080, coefficient := (-61003864088719380921272238080) }, { argument := 19863729848122893340606726144, coefficient := (-19863729848122893340606726144) }, { argument := 34889742669747091442331811840, coefficient := (-34889742669747091442331811840) }, { argument := 1967866583507076803912007680, coefficient := (-1967866583507076803912007680) }, { argument := 2021052166845105906720440320, coefficient := (-2021052166845105906720440320) }, { argument := 2021052166845105906720440320, coefficient := (-2021052166845105906720440320) }, { argument := 1967866583507076803912007680, coefficient := (-1967866583507076803912007680) }, { argument := 61003864088719380921272238080, coefficient := (-61003864088719380921272238080) }, { argument := 1967866583507076803912007680, coefficient := (-1967866583507076803912007680) }, { argument := 2655546643482208712892874752, coefficient := (-2655546643482208712892874752) }, { argument := 2606093583563426037613199360, coefficient := (-2606093583563426037613199360) }, { argument := 11883469778024501809774592, coefficient := (-11883469778024501809774592) }, { argument := 537111215074405996971425792, coefficient := (-537111215074405996971425792) }, { argument := 11946895448757438282465280, coefficient := (-11946895448757438282465280) }, { argument := 116896468404461235731431424, coefficient := (-116896468404461235731431424) }, { argument := 20502542310942653968057106432, coefficient := (-20502542310942653968057106432) }, { argument := 20502544768971301789854859264, coefficient := (-20502544768971301789854859264) }, { argument := 116894010375813413933678592, coefficient := (-116894010375813413933678592) }, { argument := 95830798569432973226016768, coefficient := (-95830798569432973226016768) }, { argument := 6377620563283318102510534656, coefficient := (-6377620563283318102510534656) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 53743618534650228409450364928, coefficient := (-53743618534650228409450364928) }, { argument := 799301110062649613431603200, coefficient := (-799301110062649613431603200) }, { argument := 47958066603758976805896192, coefficient := (-47958066603758976805896192) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 1254902742798359893087617024, coefficient := (-1254902742798359893087617024) }, { argument := 799301110062649613431603200, coefficient := (-799301110062649613431603200) }, { argument := 19367065896818000133447745536, coefficient := (-19367065896818000133447745536) }, { argument := 1238916720597106900818984960, coefficient := (-1238916720597106900818984960) }, { argument := 6377624444017102609157455872, coefficient := (-6377624444017102609157455872) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 47958066603758976805896192, coefficient := (-47958066603758976805896192) }, { argument := 1238916720597106900818984960, coefficient := (-1238916720597106900818984960) }, { argument := 47958066603758976805896192, coefficient := (-47958066603758976805896192) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 95830798569432973226016768, coefficient := (-95830798569432973226016768) }, { argument := 2925743316606765335847108608, coefficient := (-2925743316606765335847108608) }, { argument := 65706458942003690102115532800, coefficient := (-65706458942003690102115532800) }, { argument := 59432403748353037293540343808, coefficient := (-59432403748353037293540343808) }, { argument := 55469900092184207090201395200, coefficient := (-55469900092184207090201395200) }, { argument := 2712250635422256182643916800, coefficient := (-2712250635422256182643916800) }, { argument := 55469900092184207090201395200, coefficient := (-55469900092184207090201395200) }, { argument := 55382408136202843987535462400, coefficient := (-55382408136202843987535462400) }, { argument := 2926882791587863953166827520, coefficient := (-2926882791587863953166827520) }, { argument := 65706458942003690102115532800, coefficient := (-65706458942003690102115532800) }] }

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
def constantNumerator : ℤ := (-1003404160243895758493337455165440)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2352502425, 337689653, 2458017847, 4273486745, 11021097395, 9221734555,
    257983647185, 9607151241, 9221734555, 8322053135, 4273486745, 4273486745,
    8322053135, 257983647185, 8322053135, 675379293, 11021097395, 69307485,
    3132572235, 8709675, 265225389, 46518041427, 11629511751, 66304953,
    346208877, 18420462315, 8091735291, 351759959091, 2560675725, 307281087,
    8091735291, 16081043553, 2560675725, 248180691267, 15876189495, 73681874505,
    8091735291, 307281087, 15876189495, 307281087, 8091735291, 8091735291,
    346208877, 11746579, 2060239597, 515059961, 2936583, 34169949,
    16154674371, 613218558249, 64618741803, 34169949, 143756541, 13648859,
    2689439069, 142813671, 6325081, 5378876167, 6325081, 12317263,
    232696401, 12317263, 142813671, 232696401
  ]
def negativeCoefficients : Array ℕ := #[
    2712250635422256182643916800, 99668393683692558527882067968, 90684852304439122732991381504, 78831916287405071810869329920, 101651681528496013650857820160, 1360887818014150713366586327040,
    2379479157411937299133345300480, 88610330110074057140603977728, 1360887818014150713366586327040, 76757392174578622552688558080, 78831916287405071810869329920, 78831916287405071810869329920,
    76757392174578622552688558080, 2379479157411937299133345300480, 76757392174578622552688558080, 99668391765231174862088699904, 101651681528496013650857820160, 319624359546865910745661440,
    14446439577863333711645245440, 321330291380372477942169600, 1223136218183265125092294656, 214526601253521915909670699008, 214526626972894840679213039616, 1223110498810340355549954048,
    6386426550065389089148895232, 169898777022108188899037675520, 149266170025280684094973280256, 811103242591277320632514117632, 94472259509671319047451443200, 5668335570580279142847086592,
    149266170025280684094973280256, 148321447430183970904498765824, 94472259509671319047451443200, 2289062847919336060519748468736, 146432002239990544523549736960, 169898835233114956498741493760,
    149266170025280684094973280256, 5668335570580279142847086592, 146432002239990544523549736960, 5668335570580279142847086592, 149266170025280684094973280256, 149266170025280684094973280256,
    6386426550065389089148895232, 108343068277305535555960832, 19002356288190752458199269376, 19002358566363645561328893952, 108340790104412432426336256, 1260648608429415239063175168,
    149000571857975914194448416768, 1413985725658557028392971010048, 149000674050632239536150675456, 1260648608429415239063175168, 2651840120748734178977120256, 125888504435573638480003072,
    99222788415357367749084971008, 1317223619581977827022471168, 116677150452482884444880896, 99222752056824798467558735872, 116677150452482884444880896, 113606699124785966433173504,
    4292490956120291380366934016, 113606699124785966433173504, 1317223619581977827022471168, 4292490956120291380366934016
  ]
def negativeScales : Array ℕ := #[
    31, 28, 31, 31, 33, 33,
    37, 33, 33, 32, 31, 31,
    32, 37, 32, 29, 33, 26,
    31, 23, 27, 35, 33, 25,
    28, 34, 32, 38, 31, 28,
    32, 33, 31, 37, 33, 36,
    32, 28, 33, 28, 32, 32,
    28, 23, 30, 28, 21, 25,
    33, 39, 35, 25, 27, 23,
    31, 27, 22, 32, 22, 23,
    27, 23, 27, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31131549064095726, 28331122734137863, 31194848244751727, 31992766522681249, 33359548832265464, 33102390992768338,
    37908488669247628, 33161461553480180, 33102390992768338, 32954292364984813, 31992766522681249, 31992766522681249,
    32954292364984813, 37908488669247628, 32954292364984813, 29331122706368229, 33359548832265464, 26046507831714767,
    31544700631491346, 23054187455239452, 27982643662676424, 35437071304432896, 33437071477396106, 25982613326224817,
    28367067475830286, 34100590219379304, 32913801984629290, 38355800313641564, 31253877420644679, 28194983731591110,
    32913801984629290, 33904641984507110, 31253877420644679, 37852599922141403, 33886145639543957, 36100590713677838,
    32913801984629290, 28194983731591110, 33886145639543957, 28194983731591110, 32913801984629290, 32913801984629290,
    28367067475830286, 23485737320716763, 30940164989197410, 28940165162160646, 21485706984273985, 25026224758700931,
    33911232624769567, 39157610402676557, 35911233614247661, 25026224758700931, 27099052360050329, 23702277015883969,
    31324658158084816, 27089558848689068, 22592652524637716, 32324657629433232, 22592652524637716, 23554178376819980,
    27793873657134841, 23554178376819980, 27089558848689068, 27793873657134841
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
noncomputable def negativeCeiling : ℝ := 6848947009 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2712250635422256182643916800, coefficient := (-2712250635422256182643916800) }, { argument := 99668393683692558527882067968, coefficient := (-99668393683692558527882067968) }, { argument := 90684852304439122732991381504, coefficient := (-90684852304439122732991381504) }, { argument := 78831916287405071810869329920, coefficient := (-78831916287405071810869329920) }, { argument := 101651681528496013650857820160, coefficient := (-101651681528496013650857820160) }, { argument := 1360887818014150713366586327040, coefficient := (-1360887818014150713366586327040) }, { argument := 2379479157411937299133345300480, coefficient := (-2379479157411937299133345300480) }, { argument := 88610330110074057140603977728, coefficient := (-88610330110074057140603977728) }, { argument := 1360887818014150713366586327040, coefficient := (-1360887818014150713366586327040) }, { argument := 76757392174578622552688558080, coefficient := (-76757392174578622552688558080) }, { argument := 78831916287405071810869329920, coefficient := (-78831916287405071810869329920) }, { argument := 78831916287405071810869329920, coefficient := (-78831916287405071810869329920) }, { argument := 76757392174578622552688558080, coefficient := (-76757392174578622552688558080) }, { argument := 2379479157411937299133345300480, coefficient := (-2379479157411937299133345300480) }, { argument := 76757392174578622552688558080, coefficient := (-76757392174578622552688558080) }, { argument := 99668391765231174862088699904, coefficient := (-99668391765231174862088699904) }, { argument := 101651681528496013650857820160, coefficient := (-101651681528496013650857820160) }, { argument := 319624359546865910745661440, coefficient := (-319624359546865910745661440) }, { argument := 14446439577863333711645245440, coefficient := (-14446439577863333711645245440) }, { argument := 321330291380372477942169600, coefficient := (-321330291380372477942169600) }, { argument := 1223136218183265125092294656, coefficient := (-1223136218183265125092294656) }, { argument := 214526601253521915909670699008, coefficient := (-214526601253521915909670699008) }, { argument := 214526626972894840679213039616, coefficient := (-214526626972894840679213039616) }, { argument := 1223110498810340355549954048, coefficient := (-1223110498810340355549954048) }, { argument := 6386426550065389089148895232, coefficient := (-6386426550065389089148895232) }, { argument := 169898777022108188899037675520, coefficient := (-169898777022108188899037675520) }, { argument := 149266170025280684094973280256, coefficient := (-149266170025280684094973280256) }, { argument := 811103242591277320632514117632, coefficient := (-811103242591277320632514117632) }, { argument := 94472259509671319047451443200, coefficient := (-94472259509671319047451443200) }, { argument := 5668335570580279142847086592, coefficient := (-5668335570580279142847086592) }, { argument := 149266170025280684094973280256, coefficient := (-149266170025280684094973280256) }, { argument := 148321447430183970904498765824, coefficient := (-148321447430183970904498765824) }, { argument := 94472259509671319047451443200, coefficient := (-94472259509671319047451443200) }, { argument := 2289062847919336060519748468736, coefficient := (-2289062847919336060519748468736) }, { argument := 146432002239990544523549736960, coefficient := (-146432002239990544523549736960) }, { argument := 169898835233114956498741493760, coefficient := (-169898835233114956498741493760) }, { argument := 149266170025280684094973280256, coefficient := (-149266170025280684094973280256) }, { argument := 5668335570580279142847086592, coefficient := (-5668335570580279142847086592) }, { argument := 146432002239990544523549736960, coefficient := (-146432002239990544523549736960) }, { argument := 5668335570580279142847086592, coefficient := (-5668335570580279142847086592) }, { argument := 149266170025280684094973280256, coefficient := (-149266170025280684094973280256) }, { argument := 149266170025280684094973280256, coefficient := (-149266170025280684094973280256) }, { argument := 6386426550065389089148895232, coefficient := (-6386426550065389089148895232) }, { argument := 108343068277305535555960832, coefficient := (-108343068277305535555960832) }, { argument := 19002356288190752458199269376, coefficient := (-19002356288190752458199269376) }, { argument := 19002358566363645561328893952, coefficient := (-19002358566363645561328893952) }, { argument := 108340790104412432426336256, coefficient := (-108340790104412432426336256) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 149000571857975914194448416768, coefficient := (-149000571857975914194448416768) }, { argument := 1413985725658557028392971010048, coefficient := (-1413985725658557028392971010048) }, { argument := 149000674050632239536150675456, coefficient := (-149000674050632239536150675456) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 2651840120748734178977120256, coefficient := (-2651840120748734178977120256) }, { argument := 125888504435573638480003072, coefficient := (-125888504435573638480003072) }, { argument := 99222788415357367749084971008, coefficient := (-99222788415357367749084971008) }, { argument := 1317223619581977827022471168, coefficient := (-1317223619581977827022471168) }, { argument := 116677150452482884444880896, coefficient := (-116677150452482884444880896) }, { argument := 99222752056824798467558735872, coefficient := (-99222752056824798467558735872) }, { argument := 116677150452482884444880896, coefficient := (-116677150452482884444880896) }, { argument := 113606699124785966433173504, coefficient := (-113606699124785966433173504) }, { argument := 4292490956120291380366934016, coefficient := (-4292490956120291380366934016) }, { argument := 113606699124785966433173504, coefficient := (-113606699124785966433173504) }, { argument := 1317223619581977827022471168, coefficient := (-1317223619581977827022471168) }, { argument := 4292490956120291380366934016, coefficient := (-4292490956120291380366934016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
