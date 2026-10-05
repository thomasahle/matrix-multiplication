import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 16, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-573230193436908830855423607177216)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    55045571019, 6724973175, 806996781, 21250915233, 42232831539, 6724973175,
    651784400121, 41694833685, 53880155425, 21250915233, 806996781, 41694833685,
    806996781, 21250915233, 21250915233, 818546361, 484653387, 85003650741,
    21250915233, 121160799, 3382377, 1599100983, 60700598277, 6396408319,
    3382377, 5195008271, 1975930179, 68251290665, 20674976751, 915674961,
    136502531827, 915674961, 1783156503, 33687199881, 1783156503, 20674976751,
    33687199881, 1298756193, 1783156503, 1783156503, 1975930179, 3052389,
    1443091131, 54778588689, 5772368483, 3052389, 1927652591, 37594414973,
    75188802367, 240957723, 92753, 10841025, 2968095, 39451953,
    1783156503, 4957815, 18404559, 3227986737, 806996781, 4601043,
    39451953, 1783156503, 4957815, 950902215
  ]
def negativeCoefficients : Array ℕ := #[
    126926445122337061782146777088, 124053859061786957358877900800, 7443231543707217441532674048, 196005097317623392627027083264, 194764558727005523053438304256, 124053859061786957358877900800,
    3005825005067097976805611536384, 192283481545769783906260746240, 124239179722083537172142489600, 196005097317623392627027083264, 7443231543707217441532674048, 192283481545769783906260746240,
    7443231543707217441532674048, 196005097317623392627027083264, 196005097317623392627027083264, 7549757616916634623109234688, 1117534624305688980618215424, 196005073818777285730272018432,
    196005097317623392627027083264, 1117511125459582083863150592, 1996602972153647746120679424, 235985652651346947565078708224, 2239456803073747939641224331264, 235985814503079450292684587008,
    1996602972153647746120679424, 5989436752246334643551338496, 2278092394970756469913288704, 157376761449702099016304558080, 23836625303474500624214654976, 2111402707533871850163535872,
    157376704376628856463558705152, 2111402707533871850163535872, 2055839478388243643580284928, 77677394345588232803384819712, 2055839478388243643580284928, 23836625303474500624214654976,
    77677394345588232803384819712, 5989455776604082161133289472, 2055839478388243643580284928, 2055839478388243643580284928, 2278092394970756469913288704, 112613277392812449095221248,
    13310166384298532103518158848, 126310825783122978302934908928, 13310175513131005580532514816, 112613277392812449095221248, 4444864251150014019253829632, 173373637901941345731416686592,
    173373574309096994626951184384, 4444885448764797720742330368, 3504109267084865620047560704, 12798823274987973875702169600, 3504108086493244902636257280, 45485005012438610375344128,
    2055839478388243643580284928, 45727772234899160322539520, 42438023707810973947527168, 7443230651345972875833114624, 7443231543707217441532674048, 42437131346566408247967744,
    45485005012438610375344128, 2055839478388243643580284928, 45727772234899160322539520, 1096315612451783493644451840
  ]
def negativeScales : Array ℕ := #[
    35, 32, 29, 34, 35, 32,
    39, 35, 35, 34, 29, 35,
    29, 34, 34, 29, 28, 36,
    34, 26, 21, 30, 35, 32,
    21, 32, 30, 35, 34, 29,
    36, 29, 30, 34, 30, 34,
    34, 30, 30, 30, 30, 21,
    30, 35, 32, 21, 30, 35,
    36, 27, 16, 23, 21, 25,
    30, 22, 24, 31, 29, 22,
    25, 30, 22, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35679907437758465, 32646881366973095, 29587987677903891, 34306805925355797, 35297645926070321, 32646881366973095,
    39245603866630040, 35279149582452931, 35649034961360429, 34306805925355797, 29587987677903891, 35279149582452931,
    29587987677903891, 34306805925355797, 34306805925355797, 29608488889783034, 28852378094544711, 36306805752392587,
    34306805925355797, 26852347758100888, 21689606040990841, 30574613901671015, 35820991685895095, 32574614891149016,
    21689606040990841, 32274478900039942, 30879884826111423, 35990137297440301, 34267166655961305, 29770260332253290,
    36990136774243098, 29770260332253290, 30731786184240952, 34971481478751929, 30731786184240952, 34267166655961305,
    34971481478751929, 30274483482491369, 30731786184240952, 30731786184240952, 30879884826111423, 21541507401946157,
    30426515262679144, 35672893045958505, 32426516252157144, 21541507401946157, 30844197922455001, 35129799299892574,
    36129798770716979, 27844204802670006, 16501106324519055, 23369997831651248, 21501105838451461, 25233593384315263,
    30731786184240952, 22241273007839948, 24133559845276328, 31587987504940681, 29587987677903891, 22133529508833551,
    25233593384315263, 30731786184240952, 22241273007839948, 29824721750890029
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
noncomputable def negativeCeiling : ℝ := 3982092429 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 126926445122337061782146777088, coefficient := (-126926445122337061782146777088) }, { argument := 124053859061786957358877900800, coefficient := (-124053859061786957358877900800) }, { argument := 7443231543707217441532674048, coefficient := (-7443231543707217441532674048) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }, { argument := 194764558727005523053438304256, coefficient := (-194764558727005523053438304256) }, { argument := 124053859061786957358877900800, coefficient := (-124053859061786957358877900800) }, { argument := 3005825005067097976805611536384, coefficient := (-3005825005067097976805611536384) }, { argument := 192283481545769783906260746240, coefficient := (-192283481545769783906260746240) }, { argument := 124239179722083537172142489600, coefficient := (-124239179722083537172142489600) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }, { argument := 7443231543707217441532674048, coefficient := (-7443231543707217441532674048) }, { argument := 192283481545769783906260746240, coefficient := (-192283481545769783906260746240) }, { argument := 7443231543707217441532674048, coefficient := (-7443231543707217441532674048) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }, { argument := 7549757616916634623109234688, coefficient := (-7549757616916634623109234688) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 1996602972153647746120679424, coefficient := (-1996602972153647746120679424) }, { argument := 235985652651346947565078708224, coefficient := (-235985652651346947565078708224) }, { argument := 2239456803073747939641224331264, coefficient := (-2239456803073747939641224331264) }, { argument := 235985814503079450292684587008, coefficient := (-235985814503079450292684587008) }, { argument := 1996602972153647746120679424, coefficient := (-1996602972153647746120679424) }, { argument := 5989436752246334643551338496, coefficient := (-5989436752246334643551338496) }, { argument := 2278092394970756469913288704, coefficient := (-2278092394970756469913288704) }, { argument := 157376761449702099016304558080, coefficient := (-157376761449702099016304558080) }, { argument := 23836625303474500624214654976, coefficient := (-23836625303474500624214654976) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 157376704376628856463558705152, coefficient := (-157376704376628856463558705152) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 77677394345588232803384819712, coefficient := (-77677394345588232803384819712) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 23836625303474500624214654976, coefficient := (-23836625303474500624214654976) }, { argument := 77677394345588232803384819712, coefficient := (-77677394345588232803384819712) }, { argument := 5989455776604082161133289472, coefficient := (-5989455776604082161133289472) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 2278092394970756469913288704, coefficient := (-2278092394970756469913288704) }, { argument := 112613277392812449095221248, coefficient := (-112613277392812449095221248) }, { argument := 13310166384298532103518158848, coefficient := (-13310166384298532103518158848) }, { argument := 126310825783122978302934908928, coefficient := (-126310825783122978302934908928) }, { argument := 13310175513131005580532514816, coefficient := (-13310175513131005580532514816) }, { argument := 112613277392812449095221248, coefficient := (-112613277392812449095221248) }, { argument := 4444864251150014019253829632, coefficient := (-4444864251150014019253829632) }, { argument := 173373637901941345731416686592, coefficient := (-173373637901941345731416686592) }, { argument := 173373574309096994626951184384, coefficient := (-173373574309096994626951184384) }, { argument := 4444885448764797720742330368, coefficient := (-4444885448764797720742330368) }, { argument := 3504109267084865620047560704, coefficient := (-3504109267084865620047560704) }, { argument := 12798823274987973875702169600, coefficient := (-12798823274987973875702169600) }, { argument := 3504108086493244902636257280, coefficient := (-3504108086493244902636257280) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 42438023707810973947527168, coefficient := (-42438023707810973947527168) }, { argument := 7443230651345972875833114624, coefficient := (-7443230651345972875833114624) }, { argument := 7443231543707217441532674048, coefficient := (-7443231543707217441532674048) }, { argument := 42437131346566408247967744, coefficient := (-42437131346566408247967744) }, { argument := 45485005012438610375344128, coefficient := (-45485005012438610375344128) }, { argument := 2055839478388243643580284928, coefficient := (-2055839478388243643580284928) }, { argument := 45727772234899160322539520, coefficient := (-45727772234899160322539520) }, { argument := 1096315612451783493644451840, coefficient := (-1096315612451783493644451840) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-448947005291743907608119933403136)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    166779314745, 41694833685, 237720555, 1567443, 741046797, 28129545543,
    2964189221, 1567443, 18404559, 3227986737, 806996781, 4601043,
    1567443, 741046797, 28129545543, 2964189221, 1567443, 188508613,
    3676425439, 7352848181, 23563689, 43717029, 1975930179, 5493795,
    484653387, 85003650741, 21250915233, 121160799, 3052389, 1443091131,
    54778588689, 5772368483, 3052389, 484653387, 85003650741, 21250915233,
    121160799, 94624059, 44735825061, 1698136249359, 178943422973, 94624059,
    1927652591, 37594414973, 75188802367, 240957723, 3052389, 1443091131,
    54778588689, 5772368483, 3052389, 3849224259, 75070235577, 150140416083,
    481155327, 92753, 10841025, 2968095, 82946511, 3276393201,
    1596741, 4117911, 3445599, 96392733
  ]
def negativeCoefficients : Array ℕ := #[
    192283458493104299292355461120, 192283481545769783906260746240, 1096292559786298879739166720, 115656879484510082854551552, 13669900610901195133342973952, 129724631885369545284095311872,
    13669909986458870596222582784, 115656879484510082854551552, 42438023707810973947527168, 7443230651345972875833114624, 7443231543707217441532674048, 42437131346566408247967744,
    115656879484510082854551552, 13669900610901195133342973952, 129724631885369545284095311872, 13669909986458870596222582784, 115656879484510082854551552, 217335633731309833749004288,
    8477259897413535832293244928, 8477256787984237907626950656, 217336670207742475304435712, 50402302851621162848354304, 2278092394970756469913288704, 50671315179212583060111360,
    1117534624305688980618215424, 196005073818777285730272018432, 196005097317623392627027083264, 1117511125459582083863150592, 112613277392812449095221248, 13310166384298532103518158848,
    126310825783122978302934908928, 13310175513131005580532514816, 112613277392812449095221248, 1117534624305688980618215424, 196005073818777285730272018432, 196005097317623392627027083264,
    1117511125459582083863150592, 3491011599177185921951858688, 412615157913254495209062924288, 3915635599276812327390982176768, 412615440907061172996507959296, 3491011599177185921951858688,
    4444864251150014019253829632, 173373637901941345731416686592, 173373574309096994626951184384, 4444885448764797720742330368, 112613277392812449095221248, 13310166384298532103518158848,
    126310825783122978302934908928, 13310175513131005580532514816, 112613277392812449095221248, 4437853424255455637519990784, 173100177905250586511020130304, 173100114412710406307350315008,
    4437874588435515705409929216, 3504109267084865620047560704, 12798823274987973875702169600, 3504108086493244902636257280, 191261632528016766740201472, 7554848357961127220427620352,
    117818690315996252627533824, 151924100670626746809188352, 2033922653876145834833215488, 3556264152432834256941613056
  ]
def negativeScales : Array ℕ := #[
    37, 35, 27, 20, 29, 34,
    31, 20, 24, 31, 29, 22,
    20, 29, 34, 31, 20, 27,
    31, 32, 24, 25, 30, 22,
    28, 36, 34, 26, 21, 30,
    35, 32, 21, 28, 36, 34,
    26, 26, 35, 40, 37, 26,
    30, 35, 36, 27, 21, 30,
    35, 32, 21, 31, 36, 37,
    28, 16, 23, 21, 26, 31,
    20, 21, 21, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37279149409489721, 35279149582452931, 27824691414446617, 20579981549762985, 29464989410493841, 34711367193829758,
    31464990399971841, 20579981549762985, 24133559845276328, 31587987504940681, 29587987677903891, 22133529508833551,
    20579981549762985, 29464989410493841, 34711367193829758, 31464990399971841, 20579981549762985, 27490055201152773,
    31775656580530071, 32775656051354471, 24490062081367573, 25381692023304400, 30879884826111423, 22389371646829086,
    28852378094544711, 36306805752392587, 34306805925355797, 26852347758100888, 21541507401946157, 30426515262679144,
    35672893045958505, 32426516252157144, 21541507401946157, 28852378094544711, 36306805752392587, 34306805925355797,
    26852347758100888, 26495703712332241, 35380711573066003, 40627089356319397, 37380712562544003, 26495703712332241,
    30844197922455001, 35129799299892574, 36129798770716979, 27844204802670006, 21541507401946157, 30426515262679144,
    35672893045958505, 32426516252157144, 21541507401946157, 31841920581677426, 36127521959181508, 37127521430005913,
    28841927461892422, 16501106324519055, 23369997831651248, 21501105838451461, 26305677962223776, 31609461359657599,
    20606698888142346, 21973481234220725, 21716323379415823, 26522421050708350
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
noncomputable def negativeCeiling : ℝ := 3369489961 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 192283458493104299292355461120, coefficient := (-192283458493104299292355461120) }, { argument := 192283481545769783906260746240, coefficient := (-192283481545769783906260746240) }, { argument := 1096292559786298879739166720, coefficient := (-1096292559786298879739166720) }, { argument := 115656879484510082854551552, coefficient := (-115656879484510082854551552) }, { argument := 13669900610901195133342973952, coefficient := (-13669900610901195133342973952) }, { argument := 129724631885369545284095311872, coefficient := (-129724631885369545284095311872) }, { argument := 13669909986458870596222582784, coefficient := (-13669909986458870596222582784) }, { argument := 115656879484510082854551552, coefficient := (-115656879484510082854551552) }, { argument := 42438023707810973947527168, coefficient := (-42438023707810973947527168) }, { argument := 7443230651345972875833114624, coefficient := (-7443230651345972875833114624) }, { argument := 7443231543707217441532674048, coefficient := (-7443231543707217441532674048) }, { argument := 42437131346566408247967744, coefficient := (-42437131346566408247967744) }, { argument := 115656879484510082854551552, coefficient := (-115656879484510082854551552) }, { argument := 13669900610901195133342973952, coefficient := (-13669900610901195133342973952) }, { argument := 129724631885369545284095311872, coefficient := (-129724631885369545284095311872) }, { argument := 13669909986458870596222582784, coefficient := (-13669909986458870596222582784) }, { argument := 115656879484510082854551552, coefficient := (-115656879484510082854551552) }, { argument := 217335633731309833749004288, coefficient := (-217335633731309833749004288) }, { argument := 8477259897413535832293244928, coefficient := (-8477259897413535832293244928) }, { argument := 8477256787984237907626950656, coefficient := (-8477256787984237907626950656) }, { argument := 217336670207742475304435712, coefficient := (-217336670207742475304435712) }, { argument := 50402302851621162848354304, coefficient := (-50402302851621162848354304) }, { argument := 2278092394970756469913288704, coefficient := (-2278092394970756469913288704) }, { argument := 50671315179212583060111360, coefficient := (-50671315179212583060111360) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 112613277392812449095221248, coefficient := (-112613277392812449095221248) }, { argument := 13310166384298532103518158848, coefficient := (-13310166384298532103518158848) }, { argument := 126310825783122978302934908928, coefficient := (-126310825783122978302934908928) }, { argument := 13310175513131005580532514816, coefficient := (-13310175513131005580532514816) }, { argument := 112613277392812449095221248, coefficient := (-112613277392812449095221248) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 3491011599177185921951858688, coefficient := (-3491011599177185921951858688) }, { argument := 412615157913254495209062924288, coefficient := (-412615157913254495209062924288) }, { argument := 3915635599276812327390982176768, coefficient := (-3915635599276812327390982176768) }, { argument := 412615440907061172996507959296, coefficient := (-412615440907061172996507959296) }, { argument := 3491011599177185921951858688, coefficient := (-3491011599177185921951858688) }, { argument := 4444864251150014019253829632, coefficient := (-4444864251150014019253829632) }, { argument := 173373637901941345731416686592, coefficient := (-173373637901941345731416686592) }, { argument := 173373574309096994626951184384, coefficient := (-173373574309096994626951184384) }, { argument := 4444885448764797720742330368, coefficient := (-4444885448764797720742330368) }, { argument := 112613277392812449095221248, coefficient := (-112613277392812449095221248) }, { argument := 13310166384298532103518158848, coefficient := (-13310166384298532103518158848) }, { argument := 126310825783122978302934908928, coefficient := (-126310825783122978302934908928) }, { argument := 13310175513131005580532514816, coefficient := (-13310175513131005580532514816) }, { argument := 112613277392812449095221248, coefficient := (-112613277392812449095221248) }, { argument := 4437853424255455637519990784, coefficient := (-4437853424255455637519990784) }, { argument := 173100177905250586511020130304, coefficient := (-173100177905250586511020130304) }, { argument := 173100114412710406307350315008, coefficient := (-173100114412710406307350315008) }, { argument := 4437874588435515705409929216, coefficient := (-4437874588435515705409929216) }, { argument := 3504109267084865620047560704, coefficient := (-3504109267084865620047560704) }, { argument := 12798823274987973875702169600, coefficient := (-12798823274987973875702169600) }, { argument := 3504108086493244902636257280, coefficient := (-3504108086493244902636257280) }, { argument := 191261632528016766740201472, coefficient := (-191261632528016766740201472) }, { argument := 7554848357961127220427620352, coefficient := (-7554848357961127220427620352) }, { argument := 117818690315996252627533824, coefficient := (-117818690315996252627533824) }, { argument := 151924100670626746809188352, coefficient := (-151924100670626746809188352) }, { argument := 2033922653876145834833215488, coefficient := (-2033922653876145834833215488) }, { argument := 3556264152432834256941613056, coefficient := (-3556264152432834256941613056) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
